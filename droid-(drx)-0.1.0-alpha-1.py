import hashlib
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
from cryptography.hazmat.backends import default_backend
from cryptography.hazmat.primitives.ciphers.aead import AESGCM
import getpass
import sqlite3
import heapq
import multiprocessing
from collections import defaultdict
import readline
import math
import signal
import ipaddress
from decimal import Decimal, ROUND_HALF_UP
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
TX_FEE_MIN = int(0.00000001 * (10 ** DECIMALS))
# OPRAVA #6b (varianta A): TX_FEE_MAX je nově VÝHRADNĚ mempoolová politika,
# vynucovaná jen v add_transaction(). Z konsenzu (add_block, validate_fork,
# is_valid_chain) je horní mez odstraněna.
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
TX_FEE_MAX = int(0.01 * (10 ** DECIMALS))
MIN_TX_AMOUNT = int(0.00000001 * (10 ** DECIMALS))
DIFFICULTY_ADJUSTMENT_INTERVAL = 144
# OPRAVA #15: TARGET_BLOCK_TIME odstraněn - nikde se nepoužíval (LWMA-3 si
# okno počítá z BLOCK_TIME_SECONDS a N přímo v calculate_expected_target).
INITIAL_DIFFICULTY_BITS = 20
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
# Genesis konstanty jsou ověřené a platí i po zavedení state_root do hlavičky:
# nonce 38083 dává hash 0000013c... včetně state_root
# c6253efc7a5da68207e84ab2d5d238e33c23e9945cf411c0c622cb0adfca380a a splňuje
# FIXED_TARGET. verify_genesis_block() i CHECKPOINTS[0] projdou.
# Samotný state_root genesis bloku se dopočítá automaticky v create_genesis_block().
# Při JAKÉKOLI změně obsahu genesis bloku (adresa, částka, čas, data, target,
# version, chain_id) je nutné obě hodnoty níže znovu vytěžit a přepsat.
GENESIS_NONCE = 3622
GENESIS_BLOCK_EXPECTED_HASH = "0000092d034dfef99d334ec7afbefce860b0aa2ba5b72f8ea43e808a9e903cd7"
GENESIS_AMOUNT = 50 * (10 ** DECIMALS)

MAX_BLOCK_SIZE_BYTES = 1 * 1024 * 1024
MAX_MEMPOOL_SIZE_BYTES = 10 * 1024 * 1024
MAX_PENDING_TX_PER_ADDRESS = 100
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

# OPRAVA #1: původní limit byl 10 požadavků za 1 sekundu na IP, přičemž každá
# P2P zpráva je samostatné TCP spojení (_send_to_single_peer se připojí, pošle,
# zavře). Běžné stahování řetězce po dávkách proto vyčerpalo rozpočet během
# ~100 bloků a dva POCTIVÉ uzly se na LAN, localhostu nebo rychlé mobilní síti
# navzájem TRVALE zablokovaly - blacklist byl bez expirace a ukládal se na disk.
#
# Nově token bucket: RATE_LIMIT_BUCKET_CAPACITY je povolený burst,
# RATE_LIMIT_REFILL_PER_SECOND ustálený strop spojení za sekundu. Při RTT 20 ms
# a sériové komunikaci dělá sync ~18 spojení/s, refill 30/s tedy má rezervu.
# Trvalý ban je nahrazen dočasným (BAN_DURATION_SECONDS) a uděluje se až po
# dlouhodobém překračování, ne po prvním překročení burstu.
RATE_LIMIT_BUCKET_CAPACITY = 200
RATE_LIMIT_REFILL_PER_SECOND = 30.0
RATE_LIMIT_ABUSE_THRESHOLD = 600.0

# Samostatný, řádově přísnější rozpočet pro drahé dotazy (čtou z DB a generují
# velké odpovědi). Dřív spadaly do stejného limitu jako levné zprávy.
EXPENSIVE_BUCKET_CAPACITY = 40
EXPENSIVE_REFILL_PER_SECOND = 4.0

BAN_DURATION_SECONDS = 3600
BAN_DURATION_PROTOCOL = 24 * 3600

MAX_MESSAGE_SIZE = 10 * 1024 * 1024

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

# OPRAVA #9: request_blocks iteroval locator_hashes bez limitu délky a na každý
# prvek pouštěl SQL dotaz - útočník mohl poslat statisíce hashů v jedné 10MB
# zprávě. Locator se navíc staví exponenciálně, ne jako 1200 po sobě jdoucích
# hashů, což je jediné, k čemu je dobrý.
MAX_LOCATOR_HASHES = 32
TX_RATE_LIMIT = 100
TX_RATE_WINDOW = 60
SOFTWARE_VERSION = "0.1.0-alpha.1"
PROTOCOL_VERSION = 1
CHAIN_ID = 1
BLOCK_VERSION = 1
MEMPOOL_TX_EXPIRATION = 86400

CHECKPOINTS = {
    0: GENESIS_BLOCK_EXPECTED_HASH,
}

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
        if data:
            t = struct.unpack('!12I', data)
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

def is_valid_private_key(key_hex):
    if not isinstance(key_hex, str):
        return False
    if len(key_hex) != 64:
        return False
    try:
        ecdsa.SigningKey.from_string(binascii.unhexlify(key_hex), curve=ecdsa.SECP256k1)
        return True
    except (binascii.Error, ecdsa.BadSignatureError, ecdsa.MalformedPointError):
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


class Transaction:
    def __init__(self, from_address, to_address, amount, fee=0, nonce=0, public_key=None, signature=None, timestamp=None, tx_id=None, data=None, chain_id=CHAIN_ID):
        self.from_address = from_address
        self.to_address = to_address
        self.amount = amount
        self.fee = fee
        self.nonce = nonce
        self.timestamp = timestamp or get_time()
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
        
        for s in [self.from_address, self.to_address, self.public_key, self.data]:
            if s is None:
                b += struct.pack('!I', 0)
            else:
                enc = str(s).encode('utf-8')
                b += struct.pack('!I', len(enc)) + enc
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

            _check_uint(amount, 64, "Částka", minimum=1)
            _check_uint(fee, 64, "Poplatek")
            _check_uint(nonce, 64, "Nonce")

            chain_id = data.get('chain_id', CHAIN_ID)
            _check_uint(chain_id, 32, "chain_id")

            raw_timestamp = data.get('timestamp')
            if raw_timestamp is None:
                timestamp = None
            else:
                timestamp = int(raw_timestamp)
                _check_uint(timestamp, 64, "Timestamp")

            tx = Transaction(
                data['from_address'],
                data['to_address'],
                amount,
                fee,
                nonce=nonce,
                public_key=data.get('public_key'),
                signature=data.get('signature'),
                timestamp=timestamp,
                data=data.get('data'),
                chain_id=chain_id
            )
            supplied_tx_id = data.get('tx_id')
            if supplied_tx_id is not None and supplied_tx_id != tx.tx_id:
                raise ValueError(
                    f"Neplatné tx_id: dodané tx_id '{supplied_tx_id}' neodpovídá "
                    f"vypočtenému hashi obsahu transakce '{tx.tx_id}'."
                )
            return tx
        except (KeyError, ValueError, TypeError, struct.error, OverflowError) as e:
            # struct.error a OverflowError doplněny k původnímu tuple jako
            # pojistka - rozsahové kontroly výše by je už neměly připustit,
            # ale kontrakt "ven jde vždy ValueError" musí platit bezvýhradně.
            raise ValueError(f"Chyba při deserializaci transakce: {e}")

    def get_size(self):
        return len(json.dumps(self.to_dict(), separators=(',', ':'), sort_keys=True).encode('utf-8'))

    def is_valid_timestamp(self, allow_expired=False):
        # allow_expired: transakce recyklovaná z odpojeného bloku. Byla už jednou
        # potvrzená, takže její stáří nesmí být důvodem k zahození - horní mez
        # (čas v budoucnosti) ale platí vždy. Viz OPRAVA #11.
        if self.timestamp > (get_time() + 600):
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
            vk = ecdsa.VerifyingKey.from_string(binascii.unhexlify(self.public_key), curve=ecdsa.SECP256k1, hashfunc=hashlib.sha3_256)
            message = self.get_signing_data()
            
            sig_bytes = binascii.unhexlify(self.signature)
            r, s = ecdsa.util.sigdecode_string(sig_bytes, ecdsa.SECP256k1.order)
            if s > (ecdsa.SECP256k1.order // 2):
                return False
                
            return vk.verify(sig_bytes, message)
        except (ecdsa.BadSignatureError, binascii.Error, ecdsa.MalformedPointError,
                ecdsa.util.MalformedSignature, ValueError, TypeError, struct.error,
                OverflowError):
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
        except binascii.Error:
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
    b = MERKLE_LEAF_PREFIX + tx.get_signing_data()
    if tx.signature:
        enc = str(tx.signature).encode('utf-8')
        b += struct.pack('!I', len(enc)) + enc
    else:
        b += struct.pack('!I', 0)
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
    addr_bytes = str(address).encode('utf-8')
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

def compute_immature_root(immature_rewards):
    h = hashlib.sha3_256(IMMATURE_ROOT_DOMAIN)
    for block_index in sorted(immature_rewards.keys(), key=int):
        reward = immature_rewards[block_index]
        addr_bytes = str(reward['address']).encode('utf-8')
        h.update(struct.pack('!Q', int(block_index)))
        h.update(struct.pack('!I', len(addr_bytes)) + addr_bytes)
        h.update(struct.pack('!Q', int(reward['amount'])))
    return h.digest()

def compute_state_root(balance_map, nonce_map, immature_rewards, total_supply):
    return hashlib.sha3_256(
        STATE_ROOT_DOMAIN +
        compute_accounts_root(balance_map, nonce_map) +
        compute_immature_root(immature_rewards) +
        struct.pack('!Q', int(total_supply))
    ).hexdigest()

def compute_state_root_from(state):
    # Přijímá jak dict (get_state_at, is_valid_chain), tak objekt s atributy
    # (Blockchain, SimpleNamespace shadow).
    if isinstance(state, dict):
        return compute_state_root(
            state['balance_map'], state['nonce_map'],
            state.get('immature_rewards', {}), state['total_supply']
        )
    return compute_state_root(
        state.balance_map, state.nonce_map, state.immature_rewards, state.total_supply
    )

def make_state_shadow(base):
    # Mělká kopie stavu pro spekulativní aplikaci bloku přes
    # update_state_with_block(state_target=...). Hodnoty balance_map i nonce_map
    # jsou inty (immutable) a u immature_rewards se vnitřní dicty nikdy nemutují,
    # jen nahrazují celé záznamy - stejný předpoklad, na kterém stojí i
    # get_state_at().
    if isinstance(base, dict):
        return SimpleNamespace(
            balance_map=dict(base['balance_map']),
            nonce_map=dict(base['nonce_map']),
            immature_rewards=dict(base.get('immature_rewards', {})),
            total_supply=base['total_supply'],
            cumulative_work=base.get('cumulative_work', 0),
            undo_logs={},
            state_checkpoints={}
        )
    return SimpleNamespace(
        balance_map=dict(base.balance_map),
        nonce_map=dict(base.nonce_map),
        immature_rewards=dict(base.immature_rewards),
        total_supply=base.total_supply,
        cumulative_work=getattr(base, 'cumulative_work', 0),
        undo_logs={},
        state_checkpoints={}
    )

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
        self.timestamp = timestamp or get_time()
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
        # (starý formát) se zahashuje jako délka 0 a neprojde kontrolou hashe.
        for s in [self.previous_hash, self.merkle_root, self.state_root]:
            if s is None:
                b += struct.pack('!I', 0)
            else:
                enc = str(s).encode('utf-8')
                b += struct.pack('!I', len(enc)) + enc
        return hashlib.sha3_256(b).hexdigest()

    def get_size(self):
        return len(json.dumps(self.to_dict(), separators=(',', ':'), sort_keys=True).encode('utf-8'))

    def to_dict(self):
        return {
            'version': self.version,
            'chain_id': self.chain_id,
            'index': self.index,
            'timestamp': self.timestamp,
            'transactions': [tx.to_dict() for tx in self.transactions],
            'merkle_root': self.merkle_root,
            'state_root': self.state_root,
            'previous_hash': self.previous_hash,
            'target': hex(self.target)[2:],
            'nonce': self.nonce,
            'hash': self.hash
        }

    @staticmethod
    def from_dict(data):
        transactions = [Transaction.from_dict(tx_data) for tx_data in data['transactions']]
        target = int(data['target'], 16)
        ts = int(data['timestamp'])
        block = Block(
            index=data['index'], 
            transactions=transactions, 
            previous_hash=data['previous_hash'], 
            target=target, 
            nonce=data.get('nonce', 0), 
            timestamp=ts,
            version=data.get('version', BLOCK_VERSION),
            chain_id=data.get('chain_id', CHAIN_ID),
            state_root=data.get('state_root')
        )
        block.hash = data['hash']
        block.merkle_root = data.get('merkle_root', compute_merkle_root(transactions))
        return block

    def is_valid_timestamp(self, median_time_past):
        return self.timestamp > median_time_past and self.timestamp <= (get_time() + 600) and self.timestamp >= GENESIS_TIMESTAMP

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
        self.cumulative_work = 0
        self.last_target_log_idx = -1
        self.undo_logs = {}
        self.state_checkpoints = {}
        if create_genesis:
            self.create_genesis_block()

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

            if expired_transactions:
                save_mempool(self.unconfirmed_transactions)
                global p2p_node
                if 'p2p_node' in globals() and p2p_node is not None:
                    for tx in expired_transactions:
                        p2p_node.add_log(f"{Fore.YELLOW}Upozornění: Transakce {tx.tx_id} byla odstraněna z mempoolu (expirace nebo navazující).{Style.RESET_ALL}")

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
        print(f"  State root: {Fore.CYAN}{genesis_block.state_root}{Style.RESET_ALL}")
        print(f"  Hash: {Fore.CYAN}{genesis_block.hash}{Style.RESET_ALL}")

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

        work = (1 << 256) // block.target if block.target > 0 else 0
        target.cumulative_work += work
        undo_data['cumulative_work_change'] = work

        halvings = block.index // HALVING_INTERVAL_BLOCKS
        subsidy = GENESIS_AMOUNT if block.index == 0 else BLOCK_REWARD // (2 ** halvings)
        subsidy = max(0, min(subsidy, MAX_SUPPLY - target.total_supply))
            
        target.total_supply += subsidy
        undo_data['total_supply_change'] = subsidy

        target.undo_logs[block.index] = undo_data
        while len(target.undo_logs) > LAST_BLOCKS_TO_KEEP:
            oldest = min(target.undo_logs.keys())
            del target.undo_logs[oldest]
            
        # Perodické databázové checkpointy pro zrychlení rebuild_state
        if block.index > 0 and block.index % 1000 == 0:
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

            del self.undo_logs[i]
            
        self.max_block_index = to_index

    def get_state_at(self, target_index):
        if target_index == self.max_block_index:
            return {
                'balance_map': dict(self.balance_map),
                'nonce_map': dict(self.nonce_map),
                'total_supply': self.total_supply,
                'cumulative_work': self.cumulative_work,
                'immature_rewards': dict(self.immature_rewards)
            }
            
        if not hasattr(self, 'undo_logs') or target_index < self.max_block_index - LAST_BLOCKS_TO_KEEP:
            return None
        
        state = {
            'balance_map': dict(self.balance_map),
            'nonce_map': dict(self.nonce_map),
            'total_supply': self.total_supply,
            'cumulative_work': self.cumulative_work,
            'immature_rewards': dict(self.immature_rewards)
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
        
        return state

    def rebuild_state(self, up_to_index=None):
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
        
        query = "SELECT block_index, timestamp, transactions, previous_hash, target_hex, nonce, block_hash, merkle_root, version, chain_id, state_root FROM blocks WHERE block_index >= ?"
        params = [start_index]
        if up_to_index is not None:
            query += " AND block_index <= ?"
            params.append(up_to_index)
            
        c.execute(query + " ORDER BY block_index", tuple(params))
        
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
            self.update_state_with_block(block)
        conn.close()
        
        if up_to_index is not None:
            self.max_block_index = up_to_index

    def get_block_from_db(self, index):
        conn = sqlite3.connect(BLOCKCHAIN_DB, timeout=1.0)
        conn.execute("PRAGMA journal_mode=WAL;")
        c = conn.cursor()
        c.execute("SELECT block_index, timestamp, transactions, previous_hash, target_hex, nonce, block_hash, merkle_root, version, chain_id, state_root FROM blocks WHERE block_index = ?", (index,))
        row = c.fetchone()
        conn.close()
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

    def get_block(self, index):
        for b in self.chain:
            if b.index == index:
                return b
        return self.get_block_from_db(index)

    def get_last_block(self):
        if self.chain:
            return self.chain[-1]
        return self.get_block_from_db(self.max_block_index)

    def get_previous_block(self, block):
        if block.index == 0:
            return None
        prev_index = block.index - 1
        for b in reversed(self.chain):
            if b.index == prev_index:
                return b
        return self.get_block_from_db(prev_index)

    def get_next_nonce(self, address):
        with self.lock:
            expected_nonce = self.nonce_map.get(address, -1) + 1
            mempool_nonces = {tx.nonce for tx in self.unconfirmed_transactions if tx.from_address == address}
            while expected_nonce in mempool_nonces:
                expected_nonce += 1
            return expected_nonce

    def get_pending_balance(self, wallet_address):
        balance_change = 0
        for tx in self.unconfirmed_transactions:
            if tx.from_address == wallet_address:
                balance_change -= tx.amount + tx.fee
            if tx.to_address == wallet_address:
                balance_change += tx.amount
        return balance_change

    # OPRAVA #15: get_balance() odstraněna - nikdo ji nevolal. Kód, který
    # potřebuje zůstatek, si vybírá explicitně mezi get_confirmed_balance()
    # a get_pending_balance(), což je i srozumitelnější.

    def get_confirmed_balance(self, wallet_address):
        return self.balance_map.get(wallet_address, 0)

    def get_total_supply(self):
        return self.total_supply

    def get_cumulative_work(self, up_to_index=None):
        if up_to_index is None or up_to_index == self.max_block_index:
            return self.cumulative_work
        total_work = 0
        conn = sqlite3.connect(BLOCKCHAIN_DB, timeout=1.0)
        conn.execute("PRAGMA journal_mode=WAL;")
        c = conn.cursor()
        c.execute("SELECT target_hex FROM blocks WHERE block_index <= ?", (up_to_index,))
        for row in c:
            target = int(row[0], 16)
            work = (1 << 256) // target if target > 0 else 0
            total_work += work
        conn.close()
        return total_work

    def add_transaction(self, transaction, allow_expired=False):
        # allow_expired používají jen recyklační cesty po reorgu
        # (recycle_orphan_transactions a replace_chain). Ze sítě se transakce
        # přijímají vždy s allow_expired=False. Viz OPRAVA #11.
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
            
            pending_count = sum(1 for tx in self.unconfirmed_transactions if tx.from_address == transaction.from_address)
            if pending_count >= MAX_PENDING_TX_PER_ADDRESS:
                print(f"{Fore.RED}Chyba:{Style.RESET_ALL} Dosažen limit maximálního počtu nepotvrzených transakcí pro jednu adresu ({MAX_PENDING_TX_PER_ADDRESS}).")
                return False
                
            mempool_size = sum(tx.get_size() for tx in self.unconfirmed_transactions)
            tx_size = transaction.get_size()
            if mempool_size + tx_size > MAX_MEMPOOL_SIZE_BYTES:
                print(f"{Fore.RED}Chyba:{Style.RESET_ALL} Mempool je plný.")
                return False
                
            if not transaction.is_valid_timestamp(allow_expired=allow_expired):
                print(f"{Fore.RED}Chyba ověření transakce:{Style.RESET_ALL} Timestamp transakce je neplatný.")
                return False
            if self.is_tx_id_in_chain(transaction.tx_id):
                print(f"{Fore.RED}Chyba:{Style.RESET_ALL} Duplicitní TX ID: {transaction.tx_id}. Transakce již existuje v blockchainu.")
                return False
            if any(tx.tx_id == transaction.tx_id for tx in self.unconfirmed_transactions):
                print(f"{Fore.RED}Chyba:{Style.RESET_ALL} Duplicitní TX ID v mempoolu: {transaction.tx_id}.")
                return False
            if not isinstance(transaction.amount, int) or not isinstance(transaction.fee, int) or not isinstance(transaction.nonce, int):
                print(f"{Fore.RED}Chyba:{Style.RESET_ALL} Hodnoty amount, fee a nonce musí být celá čísla.")
                return False
            if transaction.from_address != "COINBASE":
                nonce_set = {tx.nonce for tx in self.unconfirmed_transactions if tx.from_address == transaction.from_address}
                if transaction.nonce in nonce_set:
                    print(f"{Fore.RED}Chyba:{Style.RESET_ALL} Duplicitní nonce {transaction.nonce} pro adresu {transaction.from_address} v mempoolu.")
                    return False
            if transaction.amount <= 0:
                print(f"{Fore.RED}Chyba:{Style.RESET_ALL} Částka transakce musí být větší než 0.")
                return False
            if transaction.amount < MIN_TX_AMOUNT:
                print(f"{Fore.RED}Chyba:{Style.RESET_ALL} Částka transakce je příliš malá. Minimální částka je {format(MIN_TX_AMOUNT / (10 ** DECIMALS), f'.{DECIMALS}f')} {TICKER}.")
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
            # OPRAVA #6b: JEDINÉ místo, kde platí horní mez poplatku. Je to
            # politika tohoto uzlu (co přepošle a co vytěží), ne pravidlo sítě.
            if not (TX_FEE_MIN <= transaction.fee <= TX_FEE_MAX):
                print(f"{Fore.RED}Chyba:{Style.RESET_ALL} Poplatek za transakci je mimo povolený rozsah ({TX_FEE_MIN/(10**DECIMALS)}-{TX_FEE_MAX/(10**DECIMALS)} {TICKER}).")
                return False
            if transaction.nonce != self.get_next_nonce(transaction.from_address):
                print(f"{Fore.RED}Chyba:{Style.RESET_ALL} Neplatná nonce ({transaction.nonce}). Očekávána: {self.get_next_nonce(transaction.from_address)}.")
                return False
            if not transaction.verify_signature():
                print(f"{Fore.RED}Chyba:{Style.RESET_ALL} Neplatný podpis transakce od {transaction.from_address}")
                return False
            current_available_balance = self.get_confirmed_balance(transaction.from_address)
            for tx_in_mempool in self.unconfirmed_transactions:
                if tx_in_mempool.from_address == transaction.from_address:
                    current_available_balance -= (tx_in_mempool.amount + tx_in_mempool.fee)
            if current_available_balance < transaction.amount + transaction.fee:
                print(f"{Fore.RED}Chyba:{Style.RESET_ALL} Nedostatečný zůstatek. K dispozici: {format(current_available_balance / (10**DECIMALS), f'.{DECIMALS}f')} {TICKER}")
                return False
            if allow_expired:
                # Recyklovaná transakce dostává novou lhůtu od okamžiku návratu
                # do mempoolu, jinak by ji nejbližší cleanup_mempool() zase
                # vyhodil a oprava by neměla žádný efekt.
                transaction.mempool_deadline = get_time() + MEMPOOL_TX_EXPIRATION
            self.unconfirmed_transactions.append(transaction)
            return True
        finally:
            self.lock.release()

    def is_tx_id_in_chain(self, tx_id, exclude_from_index=None):
        # exclude_from_index: ignoruj transakce zapsané v blocích od tohoto indexu
        # výš. Používá add_block() při mini-reorgu - nahrazovaný blok je v DB ještě
        # přítomný, ale už do řetězce nepatří, takže jeho transakce nesmí platit
        # jako duplicita. Bez toho by konkurenční blok obsahující tytéž uživatelské
        # transakce jako současný vrchol byl chybně odmítnut.
        conn = sqlite3.connect(BLOCKCHAIN_DB, timeout=1.0)
        conn.execute("PRAGMA journal_mode=WAL;")
        c = conn.cursor()
        if exclude_from_index is None:
            c.execute("SELECT 1 FROM transactions WHERE tx_id = ? LIMIT 1", (tx_id,))
        else:
            c.execute("SELECT 1 FROM transactions WHERE tx_id = ? AND block_index < ? LIMIT 1",
                      (tx_id, exclude_from_index))
        row = c.fetchone()
        conn.close()
        return row is not None

    def get_target(self):
        last_block = self.get_last_block()
        new_block_index = last_block.index + 1
        new_target = self.calculate_expected_target(new_block_index)
        
        if not hasattr(self, 'last_target_log_idx'):
            self.last_target_log_idx = -1
        if new_block_index != self.last_target_log_idx:
            global p2p_node
            if 'p2p_node' in globals() and p2p_node is not None:
                p2p_node.add_log(
                    f"{Fore.MAGENTA}ÚPRAVA TARGETU (LWMA-3) na bloku #{new_block_index}:{Style.RESET_ALL}\n"
                    f"  Starý target (hex): {hex(last_block.target)[2:]} -> Nový target (hex): {hex(new_target)[2:]}"
                )
            self.last_target_log_idx = new_block_index
        return new_target

    def get_median_time_past(self, new_block_index, chain_dict=None):
        MTP_SPAN = 11
        first_index = max(0, new_block_index - MTP_SPAN)
        if chain_dict is not None:
            timestamps = []
            for i in range(first_index, new_block_index):
                if i in chain_dict:
                    timestamps.append(chain_dict[i].timestamp)
                else:
                    b = self.get_block_from_db(i)
                    if b:
                        timestamps.append(b.timestamp)
        else:
            timestamps = [b.timestamp for b in (self.get_block(i) for i in range(first_index, new_block_index)) if b is not None]
        if not timestamps:
            return GENESIS_TIMESTAMP
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
    def calculate_expected_target(self, new_block_index, chain_dict=None):
        N = DIFFICULTY_ADJUSTMENT_INTERVAL
        
        if new_block_index <= N:
            return FIXED_TARGET
            
        first_index = new_block_index - N - 1
        if first_index < 0:
            return FIXED_TARGET
            
        blocks = []
        for i in range(first_index, new_block_index):
            if chain_dict is not None:
                if i in chain_dict:
                    blocks.append(chain_dict[i])
                else:
                    b = self.get_block_from_db(i)
                    if b is None: 
                        return FIXED_TARGET
                    blocks.append(b)
            else:
                b = self.get_block(i)
                if b is None: 
                    return FIXED_TARGET
                blocks.append(b)
                
        sum_target = 0
        t = 0
        for i in range(1, N + 1):
            solve_time = blocks[i].timestamp - blocks[i-1].timestamp
            solve_time = max(-3 * BLOCK_TIME_SECONDS, min(solve_time, 6 * BLOCK_TIME_SECONDS))
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

        def worker_now():
            return time.time() + worker_time_offset

        target = original_target
        nonce = start_nonce
        hashes_calculated = 0
        last_update_time = worker_now()
        
        while not stop_event.is_set():
            current_time = worker_now()
            if current_time - timestamp > 60:
                timestamp = int(current_time)
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
            # neprošel vlastní validací v add_block().
            for s in [previous_hash, merkle_root, state_root]:
                if s is None:
                    b += struct.pack('!I', 0)
                else:
                    enc = str(s).encode('utf-8')
                    b += struct.pack('!I', len(enc)) + enc
            
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

    def proof_of_work(self, block, num_cores):
        try:
            start_time = get_time()
            computed_hash = ""
            total_hashes_calculated = 0
            self.mining_in_progress = True
            sys.stdout.write(f"\n{Fore.YELLOW}Začínám těžit blok na zvolený počet CPU jader: {num_cores}{Style.RESET_ALL}\n")
            last_block = self.get_last_block()
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
            }
            result_queue = multiprocessing.Queue()
            stop_event = multiprocessing.Event()
            processes = []
            original_sigint = signal.getsignal(signal.SIGINT)
            signal.signal(signal.SIGINT, signal.SIG_IGN)
            core_hashes = [0] * num_cores
            core_nonces = [0] * num_cores
            core_last_hashes = [""] * num_cores
            
            for i in range(num_cores):
                p = multiprocessing.Process(target=Blockchain.mining_worker, args=(block_data, i, num_cores, result_queue, stop_event, 1.0, i))
                processes.append(p)
                p.start()
                
            signal.signal(signal.SIGINT, original_sigint)
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
            stop_event.set()
            for p in processes:
                p.terminate()
            self._shutdown_workers(processes, result_queue)
            print(f"\n{Fore.YELLOW}Těžba byla ukončena uživatelem (CTRL+C).{Style.RESET_ALL}")
            return None

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
        if not self.lock.acquire(timeout=5):
            print(f"{Fore.RED}System is busy (lock timeout). Try again later.{Style.RESET_ALL}")
            return False
        try:
            if block.chain_id != CHAIN_ID:
                p2p_node.add_log(f"{Fore.RED}Chyba ověření bloku: Zjištěno cizí chain_id.{Style.RESET_ALL}")
                return False
            if block.version != BLOCK_VERSION:
                p2p_node.add_log(f"{Fore.RED}Chyba ověření bloku: Neplatná verze bloku.{Style.RESET_ALL}")
                return False
            block_size = block.get_size()
            if block_size > MAX_BLOCK_SIZE_BYTES:
                p2p_node.add_log(f"{Fore.RED}Chyba ověření bloku: Velikost bloku ({block_size} bajtů) překračuje maximální povolenou velikost {MAX_BLOCK_SIZE_BYTES} bajtů.{Style.RESET_ALL}")
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
                            p2p_node.add_log(f"{Fore.YELLOW}Blok #{block.index} zamítnut: konkurent na stejné výšce nemá větší práci ani lepší hash (mini-reorg neproběhne).{Style.RESET_ALL}")
                            return False
                    else:
                        p2p_node.add_log(f"{Fore.RED}Blok #{block.index} zamítnut: konkurenční blok na stejné výšce nenavazuje na náš blok #{block.index - 1}.{Style.RESET_ALL}")
                        return False
                else:
                    p2p_node.add_log(f"{Fore.RED}Blok #{block.index} zamítnut: previous_hash neodpovídá našemu vrcholu #{previous_block.index} a nejde ani o konkurenta na stejné výšce.{Style.RESET_ALL}")
                    return False
                    
            if block.index != previous_block.index + 1:
                p2p_node.add_log(f"{Fore.RED}Blok #{block.index} zamítnut: nenavazuje na vrchol řetězce (očekáván index #{previous_block.index + 1}).{Style.RESET_ALL}")
                return False

            # Základní stav, proti kterému se blok validuje = stav po bloku
            # block.index - 1. Při mini-reorgu (níže) se odpojuje současný vrchol,
            # takže self.balance_map / nonce_map / immature_rewards ještě obsahují
            # blok, který se má nahradit; get_state_at() ho přes undo log odroluje.
            base_state = self.get_state_at(block.index - 1)
            if base_state is None:
                p2p_node.add_log(f"{Fore.RED}Chyba ověření bloku: Nelze rekonstruovat stav pro blok #{block.index}.{Style.RESET_ALL}")
                return False
            base_balance_map = base_state['balance_map']
            base_nonce_map = base_state['nonce_map']
            base_immature_rewards = base_state['immature_rewards']
            base_total_supply = base_state['total_supply']
                
            median_time_past = self.get_median_time_past(block.index)
            if not block.is_valid_timestamp(median_time_past):
                p2p_node.add_log(f"{Fore.RED}Chyba ověření bloku:{Style.RESET_ALL} Timestamp bloku je neplatný.")
                return False
                
            # Target se MUSÍ počítat pro výšku validovaného bloku. get_target() si
            # uvnitř bere get_last_block(), takže vrací pravidlo pro tip.index + 1.
            # V přímém pokračování to vyjde, ale při mini-reorgu je
            # block.index == tip.index a platný konkurenční blok byl zamítán s
            # "Nesprávný target bloku" - mini-reorg tak nad výškou N+1 nikdy
            # neproběhl a add_block aplikoval jiné pravidlo než validate_fork
            # a is_valid_chain. calculate_expected_target() čte bloky
            # [index-N-1, index-1], tedy vždy jen společné předky.
            if block.target != self.calculate_expected_target(block.index):
                p2p_node.add_log(f"{Fore.RED}Chyba ověření bloku: Nesprávný target bloku.{Style.RESET_ALL}")
                return False
                
            if block.merkle_root != compute_merkle_root(block.transactions):
                p2p_node.add_log(f"{Fore.RED}Chyba ověření bloku: Nesprávný Merkle root.{Style.RESET_ALL}")
                return False
            if not self.meets_difficulty(proof, block.target):
                # OPRAVA #16: doplněn chybějící log.
                p2p_node.add_log(f"{Fore.RED}Chyba ověření bloku: Hash bloku #{block.index} nesplňuje jeho target (neplatný PoW).{Style.RESET_ALL}")
                return False
            if proof != block.compute_hash():
                p2p_node.add_log(f"{Fore.RED}Chyba ověření bloku: Hash bloku neodpovídá jeho obsahu (možný útok bez reálného PoW).{Style.RESET_ALL}")
                return False
            if block.index > 0 and any(tx.data is not None for tx in block.transactions):
                p2p_node.add_log(f"{Fore.RED}Chyba ověření bloku: Nepovolená zpráva v bloku mimo genesis.{Style.RESET_ALL}")
                return False
                
            for tx in block.transactions:
                if not isinstance(tx.amount, int) or not isinstance(tx.fee, int) or not isinstance(tx.nonce, int):
                    p2p_node.add_log(f"{Fore.RED}Chyba ověření bloku: Hodnoty amount, fee a nonce musí být celá čísla.{Style.RESET_ALL}")
                    return False
                if tx.timestamp > block.timestamp + 7200:
                    p2p_node.add_log(f"{Fore.RED}Chyba ověření bloku: Transakce {tx.tx_id} má čas příliš v budoucnosti oproti bloku.{Style.RESET_ALL}")
                    return False
                if tx.chain_id != CHAIN_ID:
                    p2p_node.add_log(f"{Fore.RED}Chyba ověření bloku:{Style.RESET_ALL} Transakce patří k jinému chain_id.")
                    return False
                if not is_valid_address(tx.to_address):
                    p2p_node.add_log(f"{Fore.RED}Chyba ověření bloku:{Style.RESET_ALL} Neplatný formát adresy příjemce ({tx.to_address}).")
                    return False
                if self.is_tx_id_in_chain(tx.tx_id, exclude_from_index=block.index):
                    p2p_node.add_log(f"{Fore.RED}Chyba ověření bloku:{Style.RESET_ALL} Duplicitní TX ID {tx.tx_id} v bloku.")
                    return False
                    
            nonce_map = {}
            tx_id_set = set()
            for tx in block.transactions:
                if tx.tx_id in tx_id_set:
                    p2p_node.add_log(f"{Fore.RED}Chyba ověření bloku:{Style.RESET_ALL} Duplicitní TX ID {tx.tx_id} v bloku.")
                    return False
                tx_id_set.add(tx.tx_id)
                if tx.from_address != "COINBASE":
                    if tx.from_address in nonce_map:
                        if tx.nonce in nonce_map[tx.from_address]:
                            p2p_node.add_log(f"{Fore.RED}Chyba ověření bloku:{Style.RESET_ALL} Duplicitní nonce {tx.nonce} pro adresu {tx.from_address} v bloku.")
                            return False
                        nonce_map[tx.from_address].add(tx.nonce)
                    else:
                        nonce_map[tx.from_address] = {tx.nonce}
                        
            for sender, nonces_in_block in nonce_map.items():
                expected_nonce = base_nonce_map.get(sender, -1) + 1
                for tx_nonce in sorted(nonces_in_block):
                    if tx_nonce != expected_nonce:
                        p2p_node.add_log(f"{Fore.RED}Chyba ověření bloku: Neplatná posloupnost nonce {tx_nonce} pro adresu {sender} (očekávána přesně {expected_nonce}).{Style.RESET_ALL}")
                        return False
                    expected_nonce += 1
                    
            for tx in block.transactions:
                if not tx.verify_sender_identity() and tx.from_address != "COINBASE":
                    p2p_node.add_log(f"{Fore.RED}Chyba ověření bloku:{Style.RESET_ALL} Veřejný klíč neodpovídá adrese odesílatele.")
                    return False
                if not tx.verify_signature() and tx.from_address != "COINBASE":
                    p2p_node.add_log(f"{Fore.RED}Chyba ověření bloku:{Style.RESET_ALL} Neplatný podpis transakce.")
                    return False
                if tx.from_address != "COINBASE":
                    if tx.amount <= 0:
                        p2p_node.add_log(f"{Fore.RED}Chyba ověření bloku: Částka transakce musí být větší než 0.{Style.RESET_ALL}")
                        return False
                    if tx.amount < MIN_TX_AMOUNT:
                        p2p_node.add_log(f"{Fore.RED}Chyba ověření bloku: Částka transakce je příliš malá.{Style.RESET_ALL}")
                        return False
                    # OPRAVA #6b: konsenzus vynucuje jen dolní mez poplatku.
                    # Horní mez (TX_FEE_MAX) zůstala jen jako politika mempoolu
                    # v add_transaction() - viz komentář u konstanty.
                    if tx.fee < TX_FEE_MIN:
                        p2p_node.add_log(f"{Fore.RED}Chyba ověření bloku: Poplatek transakce je nižší než minimum.{Style.RESET_ALL}")
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
                        p2p_node.add_log(f"{Fore.RED}Chyba ověření bloku: Transakce na vlastní adresu není povolena.{Style.RESET_ALL}")
                        return False
                        
            coinbase_txs = [tx for tx in block.transactions if tx.from_address == "COINBASE"]
            if len(coinbase_txs) != 1:
                p2p_node.add_log(f"{Fore.RED}Chyba ověření bloku: Nesprávný počet coinbase transakcí (očekávána 1).{Style.RESET_ALL}")
                return False
            if block.transactions[0].from_address != "COINBASE":
                p2p_node.add_log(f"{Fore.RED}Chyba ověření bloku: Coinbase transakce musí být první v bloku.{Style.RESET_ALL}")
                return False
                
            coinbase_tx = coinbase_txs[0]

            # Nonce coinbase transakce musí být rovna výšce bloku. Je to jediné, co
            # dělá tx_id coinbase transakcí unikátní napříč celým řetězcem (obdoba
            # BIP30) - bez tohoto pravidla na tom stála jen konvence těžaře v mine()
            # a dva bloky téhož těžaře se stejnou odměnou i časem by kolidovaly.
            if coinbase_tx.nonce != block.index:
                p2p_node.add_log(f"{Fore.RED}Chyba ověření bloku: Nonce coinbase transakce ({coinbase_tx.nonce}) musí být rovna výšce bloku ({block.index}).{Style.RESET_ALL}")
                return False

            halvings = block.index // HALVING_INTERVAL_BLOCKS
            expected_reward = BLOCK_REWARD // (2 ** halvings) if block.index > 0 else GENESIS_AMOUNT
            expected_reward = max(0, min(expected_reward, MAX_SUPPLY - base_total_supply))
                
            total_fees = sum(tx.fee for tx in block.transactions if tx.from_address != "COINBASE")
            if coinbase_tx.amount != expected_reward + total_fees:
                p2p_node.add_log(f"{Fore.RED}Chyba ověření bloku: Nesprávná coinbase odměna.{Style.RESET_ALL}")
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
                        p2p_node.add_log(f"{Fore.RED}Chyba ověření bloku: Nedostatečný zůstatek pro transakci {tx.tx_id} od {tx.from_address}.{Style.RESET_ALL}")
                        return False
                    temp_balance_changes[tx.from_address] -= (tx.amount + tx.fee)
                    temp_balance_changes[tx.to_address] += tx.amount
                else:
                    pass

            # Ověření state rootu: blok se spekulativně aplikuje na kopii
            # základního stavu a výsledný root se porovná s hlavičkou. Teprve po
            # shodě se blok zapisuje do DB a promítá do self.
            try:
                shadow_state = make_state_shadow(base_state)
                self.update_state_with_block(block, state_target=shadow_state)
                expected_state_root = compute_state_root_from(shadow_state)
            except ValueError as e:
                p2p_node.add_log(f"{Fore.RED}Chyba ověření bloku: Neplatný stav po aplikaci bloku #{block.index} ({e}).{Style.RESET_ALL}")
                return False
            if block.state_root != expected_state_root:
                p2p_node.add_log(f"{Fore.RED}Chyba ověření bloku: Nesprávný state root bloku #{block.index} (očekáván {expected_state_root}, přijat {block.state_root}).{Style.RESET_ALL}")
                return False

            if is_mini_reorg:
                p2p_node.add_log(f"{Fore.YELLOW}Detekován lepší konkurenční blok na stejné výšce. Provádím bleskový mini-reorg (Undo).{Style.RESET_ALL}")
                self.chain.pop()
                self.rollback_state(block_to_remove.index - 1)
                try:
                    conn = sqlite3.connect(BLOCKCHAIN_DB, timeout=1.0)
                    conn.execute("PRAGMA journal_mode=WAL;")
                    c = conn.cursor()
                    c.execute("DELETE FROM blocks WHERE block_index = ?", (block_to_remove.index,))
                    c.execute("DELETE FROM transactions WHERE block_index = ?", (block_to_remove.index,))
                    conn.commit()
                    conn.close()
                except Exception as e:
                    if 'conn' in locals():
                        try:
                            conn.rollback()
                            conn.close()
                        except:
                            pass
                    p2p_node.add_log(f"{Fore.RED}Kritická chyba DB: Selhal rollback při mini-reorgu ({e}).{Style.RESET_ALL}")
                    return False
                    
            block.hash = proof
            
            try:
                conn = sqlite3.connect(BLOCKCHAIN_DB, timeout=1.0)
                conn.execute("PRAGMA journal_mode=WAL;")
                c = conn.cursor()
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
            except Exception as e:
                if 'conn' in locals():
                    try:
                        conn.rollback()
                        conn.close()
                    except:
                        pass
                p2p_node.add_log(f"{Fore.RED}Kritická chyba DB: Selhal zápis bloku #{block.index} ({e}).{Style.RESET_ALL}")
                return False
                
            self.chain.append(block)
            self.max_block_index = block.index
            if len(self.chain) > LAST_BLOCKS_TO_KEEP:
                self.chain = self.chain[-LAST_BLOCKS_TO_KEEP:]
            self.update_state_with_block(block)
            
            confirmed_tx_ids = {tx.tx_id for tx in block.transactions if tx.from_address != "COINBASE"}
            self.unconfirmed_transactions = [
                tx for tx in self.unconfirmed_transactions
                if tx.tx_id not in confirmed_tx_ids
            ]

            # Transakce odpojeného bloku, které nový vrchol nepřebírá, musí zpět do
            # mempoolu - jinak by mini-reorgem nenávratně zmizely. Volá se až tady,
            # protože recycle_orphan_transactions() se ptá is_tx_id_in_chain() a
            # add_transaction() validuje proti stavu; obojí už je aktuální.
            if is_mini_reorg and block_to_remove is not None:
                self.recycle_orphan_transactions([block_to_remove])
            
            self.resolve_orphans(block.hash)
            return True
        finally:
            self.lock.release()

    def add_orphan_block(self, block):
        if block.hash in self.orphan_pool:
            return
        if len(self.orphan_pool) > 100:
            oldest_hash = next(iter(self.orphan_pool))
            oldest_block = self.orphan_pool.pop(oldest_hash)
            if oldest_block.previous_hash in self.orphan_parents:
                if oldest_hash in self.orphan_parents[oldest_block.previous_hash]:
                    self.orphan_parents[oldest_block.previous_hash].remove(oldest_hash)
                if not self.orphan_parents[oldest_block.previous_hash]:
                    del self.orphan_parents[oldest_block.previous_hash]
        self.orphan_pool[block.hash] = block
        self.orphan_parents[block.previous_hash].append(block.hash)

    def resolve_orphans(self, parent_hash):
        if parent_hash not in self.orphan_parents:
            return
        for child_hash in list(self.orphan_parents[parent_hash]):
            if child_hash in self.orphan_pool:
                child_block = self.orphan_pool.pop(child_hash)
                self.orphan_parents[parent_hash].remove(child_hash)
                if child_block.previous_hash == parent_hash:
                    if self.add_block(child_block, child_block.hash):
                        p2p_node.add_log(f"{Fore.GREEN}Orphan blok {child_block.index} přidán do chainu.{Style.RESET_ALL}")
                        self.resolve_orphans(child_block.hash)
                    else:
                        self.recycle_orphan_transactions([child_block])
                        p2p_node.add_log(f"{Fore.RED}Orphan blok {child_block.index} nevalidní, zahazuji a recykluji tx.{Style.RESET_ALL}")

    def recycle_orphan_transactions(self, orphaned_blocks):
        orphaned_transactions = []
        for block in orphaned_blocks:
            for tx in block.transactions:
                if tx.from_address == "COINBASE":
                    p2p_node.add_log(f"{Fore.YELLOW}COINBASE transakce {tx.tx_id} z osiřelého bloku #{block.index} zanikla (přirozené chování).{Style.RESET_ALL}")
                elif not self.is_tx_id_in_chain(tx.tx_id):
                    orphaned_transactions.append(tx)
        orphaned_transactions.sort(key=lambda x: (x.from_address, x.nonce))
        
        for tx in orphaned_transactions:
            # OPRAVA #11: allow_expired=True - tahle transakce už jednou byla v
            # bloku, takže ji nesmíme zahodit jen proto, že byla podepsána před
            # víc než MEMPOOL_TX_EXPIRATION. Bez toho ji uživatel po reorgu
            # nenávratně ztratil a musel ji podepsat znovu.
            if self.add_transaction(tx, allow_expired=True):
                p2p_node.add_log(f"{Fore.GREEN}Osiřelá uživatelská transakce {tx.tx_id} přidána zpět do mempoolu.{Style.RESET_ALL}")
            else:
                reason = "Neznámý důvod"
                if self.is_tx_id_in_chain(tx.tx_id):
                    reason = "Již existuje v blockchainu"
                elif any(t.tx_id == tx.tx_id for t in self.unconfirmed_transactions):
                    reason = "Již existuje v mempoolu"
                elif tx.nonce != self.get_next_nonce(tx.from_address):
                    reason = f"Navazující chyba nonce (Máte {tx.nonce}, ale síť čeká na {self.get_next_nonce(tx.from_address)}. Pravděpodobně selhala předchozí transakce.)"
                elif self.get_confirmed_balance(tx.from_address) - sum(t.amount + t.fee for t in self.unconfirmed_transactions if t.from_address == tx.from_address) < tx.amount + tx.fee:
                    reason = "Nedostatečný zůstatek (pokus o utracení zrušené coinbase odměny nebo již utracených prostředků)"
                else:
                    reason = "Jiná chyba ověření (např. čas, podpis)"
                p2p_node.add_log(f"{Fore.RED}Osiřelá uživatelská transakce {tx.tx_id} zamítnuta z mempoolu. Důvod: {reason}.{Style.RESET_ALL}")

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
                current_reward = BLOCK_REWARD // (2 ** halvings)
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
                target = self.get_target()
            
                while pq:
                    _, _, _, sender = heapq.heappop(pq)
                    if sender not in tx_by_sender or not tx_by_sender[sender]:
                        continue
                    tx = tx_by_sender[sender].pop(0)
                
                    test_reward = current_reward + total_fees + tx.fee
                    test_coinbase = Transaction("COINBASE", miner_address, test_reward, nonce=new_block_index, public_key=None, signature=None, timestamp=mining_reward.timestamp, data=None, chain_id=CHAIN_ID)
                
                    test_block = Block(
                        index=new_block_index,
                        transactions=[test_coinbase] + selected_txs + [tx],
                        previous_hash=last_block_hash,
                        target=target,
                        nonce=sys.maxsize,
                        version=BLOCK_VERSION,
                        chain_id=CHAIN_ID,
                        state_root="0" * 64
                    )
                    test_block.merkle_root = "0" * 64
                
                    if test_block.get_size() > MAX_BLOCK_SIZE_BYTES:
                        continue
                    
                    selected_txs.append(tx)
                    total_fees += tx.fee
                    expected_nonces[sender] += 1
                
                    if tx_by_sender[sender]:
                        next_tx = tx_by_sender[sender][0]
                        if next_tx.nonce == expected_nonces[sender]:
                            heapq.heappush(pq, (-next_tx.fee, next_tx.timestamp, next_tx.tx_id, sender))
                    
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
                if final_reward == 0:
                    print(f"{Fore.YELLOW}Upozornění:{Style.RESET_ALL} Maximální nabídka byla dosažena a nejsou k dispozici žádné transakce k vytěžení.")
                    return False
                
                new_block_transactions = [Transaction("COINBASE", miner_address, final_reward, nonce=new_block_index, public_key=None, signature=None, timestamp=mining_reward.timestamp, data=None, chain_id=CHAIN_ID)] + selected_txs
            
                new_block = Block(
                    index=new_block_index,
                    transactions=new_block_transactions,
                    previous_hash=last_block_hash,
                    target=target,
                    version=BLOCK_VERSION,
                    chain_id=CHAIN_ID
                )

                # State root se počítá až nad finálním seznamem transakcí, ale ještě
                # před PoW - přechod stavu nezávisí na nonce, takže root je v tuhle
                # chvíli už jednoznačně určený a může vstoupit do hashovaného headeru.
                try:
                    mining_shadow = make_state_shadow(self)
                    self.update_state_with_block(new_block, state_target=mining_shadow)
                    new_block.state_root = compute_state_root_from(mining_shadow)
                except ValueError as e:
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
                user_cores = int(input(f"Vyberte počet dostupných CPU jader: "))
                if 1 <= user_cores <= num_cores:
                    num_cores = user_cores
                else:
                    print(f"{Fore.RED}Neplatný počet. Používám všechna {num_cores} jádra.{Style.RESET_ALL}")
            except ValueError:
                print(f"{Fore.RED}Neplatný vstup. Používám všechna {num_cores} jádra.{Style.RESET_ALL}")
                
            if self.get_last_block().hash != last_block_hash:
                print(f"{Fore.YELLOW}Těžba zrušena: Mezitím přišel nový blok od jiného uzlu.{Style.RESET_ALL}")
                return False
                
            proof = self.proof_of_work(new_block, num_cores)
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
                    print(f"  Odměna za blok: {Fore.CYAN}{format(current_reward / (10 ** DECIMALS), f'.{DECIMALS}f')} {TICKER}{Style.RESET_ALL}")
                    print(f"  Poplatky z transakcí: {Fore.CYAN}{format(total_fees / (10 ** DECIMALS), f'.{DECIMALS}f')} {TICKER}{Style.RESET_ALL}")
                    print(f"  Celková odměna pro těžaře: {Fore.CYAN}{format(final_reward / (10 ** DECIMALS), f'.{DECIMALS}f')} {TICKER}{Style.RESET_ALL}")
                    print(f"  Těžařská adresa: {Fore.CYAN}{miner_address}{Style.RESET_ALL}")
                    
                    save_mempool(self.unconfirmed_transactions)
                    p2p_node.send_data_to_peers({'type': 'new_block', 'data': new_block.to_dict()})
                    return new_block.index
            return False
        except KeyboardInterrupt:
            self.mining_in_progress = False
            print(f"\n{Fore.YELLOW}Těžba byla ukončena uživatelem (CTRL+C).{Style.RESET_ALL}")
            return False

    def validate_fork(self, fork_index, new_chain_tail):
        state = self.get_state_at(fork_index - 1)
        if state is None:
            return False, None, {}
            
        balance_map = state['balance_map']
        nonce_map = state['nonce_map']
        total_supply = state['total_supply']
        immature_rewards = state['immature_rewards']
        cumulative_work = state['cumulative_work']
        
        previous_block = self.get_block(fork_index - 1)
        if not previous_block:
            return False, None, {}
            
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
                
            median_time_past = self.get_median_time_past(current_block.index, chain_dict=chain_window)
            if not current_block.is_valid_timestamp(median_time_past):
                return False, None, {}
                
            expected_target = self.calculate_expected_target(current_block.index, chain_dict=chain_window)
            if current_block.target != expected_target:
                return False, None, {}
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

            # Stejné pravidlo jako v add_block(): nonce coinbase = výška bloku.
            if coinbase_tx.nonce != current_block.index:
                return False, None, {}

            halvings = current_block.index // HALVING_INTERVAL_BLOCKS
            expected_reward = BLOCK_REWARD // (2 ** halvings)
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
            
            for tx in current_block.transactions:
                if not isinstance(tx.amount, int) or not isinstance(tx.fee, int) or not isinstance(tx.nonce, int):
                    return False, None, {}
                if tx.timestamp > current_block.timestamp + 7200:
                    return False, None, {}
                if tx.chain_id != CHAIN_ID:
                    return False, None, {}
                if not is_valid_address(tx.to_address):
                    return False, None, {}
                    
                if tx.tx_id in fork_tx_ids:
                    return False, None, {}
                    
                conn = sqlite3.connect(BLOCKCHAIN_DB, timeout=1.0)
                conn.execute("PRAGMA journal_mode=WAL;")
                c = conn.cursor()
                c.execute("SELECT block_index FROM transactions WHERE tx_id = ?", (tx.tx_id,))
                row = c.fetchone()
                conn.close()
                if row and row[0] < fork_index:
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
                    
                    if tx.from_address not in undo_data['nonce_restores']:
                        undo_data['nonce_restores'][tx.from_address] = nonce_map.get(tx.from_address, -1)
                else:
                    immature_rewards[current_block.index] = {'address': tx.to_address, 'amount': tx.amount}
                    undo_data['immature_removes'].append(current_block.index)
            
            for addr, change in temp_balance_changes.items():
                balance_map[addr] = balance_map.get(addr, 0) + change
                undo_data['balance_changes'][addr] -= change
                touched_addresses.add(addr)

            prune_zero_balances(balance_map, touched_addresses)

            # Stav po tomto bloku musí odpovídat state rootu v jeho hlavičce.
            try:
                expected_state_root = compute_state_root(balance_map, nonce_map, immature_rewards, total_supply)
            except ValueError:
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
            'state_checkpoints': new_state_checkpoints
        }
        return True, state_dict, new_undo_logs

    def is_valid_chain(self, chain_iterable=None):
        global p2p_node
        if 'p2p_node' not in globals() or p2p_node is None:
            class DummyNode:
                def add_log(self, msg):
                    print(msg)
            p2p_node = DummyNode()

        seen_tx_ids = set()
        nonce_maps = {}
        
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
            state_checkpoints={}
        )
        
        chain_window = {}
        previous_block = None
        
        def get_iterable():
            if chain_iterable is not None:
                for b in chain_iterable:
                    yield b
            else:
                conn = sqlite3.connect(BLOCKCHAIN_DB, timeout=1.0)
                conn.execute("PRAGMA journal_mode=WAL;")
                c = conn.cursor()
                c.execute("SELECT block_index, timestamp, transactions, previous_hash, target_hex, nonce, block_hash, merkle_root, version, chain_id, state_root FROM blocks ORDER BY block_index")
                for row in c:
                    yield Block.from_dict({
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
                conn.close()

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
                    
                self.update_state_with_block(current_block, state_target=state)
                try:
                    expected_state_root = compute_state_root_from(state)
                except ValueError as e:
                    p2p_node.add_log(f"{Fore.RED}Chyba ověření řetězce: Neplatný stav po genesis bloku ({e}).{Style.RESET_ALL}")
                    return False, None
                if current_block.state_root != expected_state_root:
                    p2p_node.add_log(f"{Fore.RED}Chyba ověření řetězce: Nesprávný state root genesis bloku (očekáván {expected_state_root}).{Style.RESET_ALL}")
                    return False, None
                seen_tx_ids.add(genesis_tx.tx_id)
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

            median_time_past = self.get_median_time_past(current_block.index, chain_dict=chain_window)
            if not current_block.is_valid_timestamp(median_time_past):
                p2p_node.add_log(f"{Fore.RED}Chyba ověření bloku: Timestamp bloku #{current_block.index} v řetězci je neplatný.{Style.RESET_ALL}")
                return False, None
                
            if current_block.target != self.calculate_expected_target(current_block.index, chain_dict=chain_window):
                p2p_node.add_log(f"{Fore.RED}Chyba ověření řetězce: Nesprávný target bloku #{current_block.index}.{Style.RESET_ALL}")
                return False, None
            if current_block.merkle_root != compute_merkle_root(current_block.transactions):
                p2p_node.add_log(f"{Fore.RED}Chyba ověření řetězce: Nesprávný Merkle root v bloku #{current_block.index}.{Style.RESET_ALL}")
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

            # Stejné pravidlo jako v add_block() a validate_fork():
            # nonce coinbase = výška bloku.
            if coinbase_tx.nonce != current_block.index:
                p2p_node.add_log(f"{Fore.RED}Chyba ověření řetězce: Nonce coinbase transakce ({coinbase_tx.nonce}) v bloku #{current_block.index} neodpovídá výšce bloku.{Style.RESET_ALL}")
                return False, None

            halvings = current_block.index // HALVING_INTERVAL_BLOCKS
            expected_reward = BLOCK_REWARD // (2 ** halvings)
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
                if tx.chain_id != CHAIN_ID:
                    p2p_node.add_log(f"{Fore.RED}Chyba ověření řetězce: Transakce má nesprávné chain_id.{Style.RESET_ALL}")
                    return False, None
                if not is_valid_address(tx.to_address):
                    p2p_node.add_log(f"{Fore.RED}Chyba ověření řetězce: Neplatný formát adresy příjemce ({tx.to_address}) v bloku #{current_block.index}.{Style.RESET_ALL}")
                    return False, None
                if tx.tx_id in seen_tx_ids:
                    p2p_node.add_log(f"{Fore.RED}Chyba ověření řetězce: Duplicitní TX ID {tx.tx_id} v řetězci.{Style.RESET_ALL}")
                    return False, None
                if tx.tx_id in block_tx_ids:
                    p2p_node.add_log(f"{Fore.RED}Chyba ověření bloku: Duplicitní TX ID {tx.tx_id} v bloku #{current_block.index}.{Style.RESET_ALL}")
                    return False, None
                    
                block_tx_ids.add(tx.tx_id)
                seen_tx_ids.add(tx.tx_id)
                
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
                if not tx.verify_signature() and tx.from_address != "COINBASE":
                    return False, None

            for sender, nonces_in_block in block_nonce_map.items():
                expected_nonce = (max(nonce_maps[sender]) if sender in nonce_maps else -1) + 1
                for tx_nonce in sorted(nonces_in_block):
                    if tx_nonce != expected_nonce:
                        p2p_node.add_log(f"{Fore.RED}Chyba ověření řetězce: Neplatná posloupnost nonce {tx_nonce} pro adresu {sender} v bloku #{current_block.index} (očekávána přesně {expected_nonce}).{Style.RESET_ALL}")
                        return False, None
                    expected_nonce += 1
                if sender in nonce_maps:
                    nonce_maps[sender].update(nonces_in_block)
                else:
                    nonce_maps[sender] = set(nonces_in_block)

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

            self.update_state_with_block(current_block, state_target=state)

            try:
                expected_state_root = compute_state_root_from(state)
            except ValueError as e:
                p2p_node.add_log(f"{Fore.RED}Chyba ověření řetězce: Neplatný stav po bloku #{current_block.index} ({e}).{Style.RESET_ALL}")
                return False, None
            if current_block.state_root != expected_state_root:
                p2p_node.add_log(f"{Fore.RED}Chyba ověření řetězce: Nesprávný state root bloku #{current_block.index} (očekáván {expected_state_root}, v bloku {current_block.state_root}).{Style.RESET_ALL}")
                return False, None

            previous_block = current_block

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
            'state_checkpoints': state.state_checkpoints
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
        conn = sqlite3.connect(BLOCKCHAIN_DB, timeout=1.0)
        conn.execute("PRAGMA journal_mode=WAL;")
        c = conn.cursor()
        c.execute("SELECT block_index FROM blocks WHERE block_hash = ?", (block_hash,))
        row = c.fetchone()
        conn.close()
        if row:
            block_index = row[0]
            return self.max_block_index - block_index + 1
        return 0

    def replace_chain(self, fork_index, new_blocks_data):
        if not self.lock.acquire(timeout=5):
            print(f"{Fore.RED}System is busy (lock timeout). Try again later.{Style.RESET_ALL}")
            return False
        try:
            reorg_depth = self.max_block_index - fork_index + 1
            if reorg_depth > MAX_REORG_DEPTH:
                global p2p_node
                if 'p2p_node' in globals() and hasattr(p2p_node, 'add_log'):
                    p2p_node.add_log(f"{Fore.RED}Reorg zamítnut: hloubka {reorg_depth} překračuje limit MAX_REORG_DEPTH ({MAX_REORG_DEPTH}).{Style.RESET_ALL}")
                return False

            new_chain_tail = [Block.from_dict(b) for b in new_blocks_data]
            
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
                is_valid, new_state = self.is_valid_chain(chain_iterable=proposed_chain_iterator())
                new_undo_logs = {}
            else:
                is_valid, new_state, new_undo_logs = self.validate_fork(fork_index, new_chain_tail)
                if not is_valid and new_state is None:
                    def proposed_chain_iterator():
                        conn = sqlite3.connect(BLOCKCHAIN_DB, timeout=1.0)
                        conn.execute("PRAGMA journal_mode=WAL;")
                        c = conn.cursor()
                        c.execute("SELECT block_index, timestamp, transactions, previous_hash, target_hex, nonce, block_hash, merkle_root, version, chain_id, state_root FROM blocks WHERE block_index < ? ORDER BY block_index", (fork_index,))
                        for row in c:
                            yield Block.from_dict({
                                'index': row[0], 'timestamp': row[1], 'transactions': json.loads(row[2]),
                                'previous_hash': row[3], 'target': row[4], 'nonce': row[5], 'hash': row[6],
                                'merkle_root': row[7], 'version': row[8], 'chain_id': row[9], 'state_root': row[10]
                            })
                        conn.close()
                        for b in new_chain_tail: yield b
                    is_valid, new_state = self.is_valid_chain(chain_iterable=proposed_chain_iterator())
                    new_undo_logs = {}
            
            if not is_valid:
                return False

            conn = sqlite3.connect(BLOCKCHAIN_DB, timeout=1.0)
            conn.execute("PRAGMA journal_mode=WAL;")
            c = conn.cursor()
            
            orphaned_transactions = []
            if fork_index <= self.max_block_index:
                c.execute("SELECT block_index, transactions FROM blocks WHERE block_index >= ? ORDER BY block_index", (fork_index,))
                new_tx_ids = set(tx.tx_id for block in new_chain_tail for tx in block.transactions)
                
                for row in c.fetchall():
                    local_block_index = row[0]
                    local_transactions = json.loads(row[1])
                    for tx_data in local_transactions:
                        tx = Transaction.from_dict(tx_data)
                        if tx.from_address == "COINBASE":
                            p2p_node.add_log(f"{Fore.YELLOW}COINBASE transakce {tx.tx_id} z osiřelého bloku #{local_block_index} zanikla (přirozené chování).{Style.RESET_ALL}")
                        elif tx.tx_id not in new_tx_ids:
                            orphaned_transactions.append(tx)
                
                if reorg_depth > 0:
                    p2p_node.add_log(
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
            conn.close()
            
            self.balance_map = new_state['balance_map']
            self.nonce_map = new_state['nonce_map']
            self.total_supply = new_state['total_supply']
            self.cumulative_work = new_state['cumulative_work']
            self.immature_rewards = new_state.get('immature_rewards', {})
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
            
            conn = sqlite3.connect(BLOCKCHAIN_DB, timeout=1.0)
            conn.execute("PRAGMA journal_mode=WAL;")
            c = conn.cursor()
            c.execute("SELECT block_index, timestamp, transactions, previous_hash, target_hex, nonce, block_hash, merkle_root, version, chain_id, state_root FROM blocks WHERE block_index >= ? ORDER BY block_index", (self.max_block_index - LAST_BLOCKS_TO_KEEP + 1,))
            rows = c.fetchall()
            self.chain = [Block.from_dict({
                'index': row[0], 'timestamp': row[1], 'transactions': json.loads(row[2]),
                'previous_hash': row[3], 'target': row[4], 'nonce': row[5], 'hash': row[6],
                'merkle_root': row[7], 'version': row[8], 'chain_id': row[9], 'state_root': row[10]
            }) for row in rows]
            conn.close()

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
            
            for tx in combined_transactions:
                if self.add_transaction(tx, allow_expired=(tx.tx_id in orphaned_tx_ids)):
                    p2p_node.add_log(f"{Fore.GREEN}Osiřelá/čekající transakce {tx.tx_id} ponechána nebo přidána do mempoolu.{Style.RESET_ALL}")
                else:
                    reason = "Neznámý důvod"
                    if self.is_tx_id_in_chain(tx.tx_id):
                        reason = "Již existuje v novém řetězci"
                    elif any(t.tx_id == tx.tx_id for t in self.unconfirmed_transactions):
                        reason = "Již existuje v mempoolu"
                    elif tx.nonce != self.get_next_nonce(tx.from_address):
                        reason = f"Navazující chyba nonce (Máte {tx.nonce}, ale síť čeká na {self.get_next_nonce(tx.from_address)}.)"
                    elif self.get_confirmed_balance(tx.from_address) - sum(t.amount + t.fee for t in self.unconfirmed_transactions if t.from_address == tx.from_address) < tx.amount + tx.fee:
                        reason = "Nedostatečný zůstatek"
                    else:
                        reason = "Jiná chyba ověření (např. čas, podpis, plný mempool)"
                    p2p_node.add_log(f"{Fore.RED}Transakce {tx.tx_id} zamítnuta z mempoolu po reorgu. Důvod: {reason}.{Style.RESET_ALL}")
            
            save_mempool(self.unconfirmed_transactions)
            return True
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
        
        conn = sqlite3.connect(BLOCKCHAIN_DB, timeout=1.0)
        conn.execute("PRAGMA journal_mode=WAL;")
        c = conn.cursor()
        c.execute("SELECT block_index FROM transactions WHERE tx_id = ?", (tx_id,))
        row = c.fetchone()
        if row:
            b_idx = row[0]
            c.execute("SELECT transactions FROM blocks WHERE block_index = ?", (b_idx,))
            block_row = c.fetchone()
            if block_row:
                transactions = json.loads(block_row[0])
                for tx_data in transactions:
                    if tx_data['tx_id'] == tx_id:
                        conn.close()
                        return Transaction.from_dict(tx_data), f"Blok #{b_idx}"
        conn.close()
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
            kdf = Argon2id(
                salt=salt,
                length=32,
                iterations=3,
                lanes=4,
                memory_cost=65536
            )
            key = kdf.derive(password.encode())
            aesgcm = AESGCM(key)
            decrypted = aesgcm.decrypt(nonce, ciphertext_and_tag, None)
            return json.loads(decrypted.decode())
        except Exception as e:
            print(f"{Fore.RED}Chyba při dešifrování adresáře (špatné heslo nebo poškozený soubor).{Style.RESET_ALL}")
            return {}
    return {}

def save_address_book(address_book, password):
    try:
        data_json = json.dumps(address_book, indent=4).encode()
        salt = os.urandom(16)
        kdf = Argon2id(
            salt=salt,
            length=32,
            iterations=3,
            lanes=4,
            memory_cost=65536
        )
        key = kdf.derive(password.encode())
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

def load_blacklist():
    # OPRAVA #1: blacklist je nově slovník {ip: expirace}, kde None znamená
    # trvalý ban (ten uděluje jen uživatel ručně z menu). Starý formát byl
    # prostý seznam IP bez jakékoli expirace - ten načteme a zmigrujeme na
    # dočasné bany, aby se uzly zablokované kvůli chybě #1 samy uvolnily.
    if os.path.exists(BLACKLIST_FILE):
        try:
            with open(BLACKLIST_FILE, 'r') as f:
                raw = json.load(f)
            if isinstance(raw, list):
                now = time.time()
                print(f"{Fore.YELLOW}Blacklist ve starém formátu převeden na dočasné bany ({len(raw)} IP).{Style.RESET_ALL}")
                return {str(ip): now + BAN_DURATION_SECONDS for ip in raw}
            if isinstance(raw, dict):
                out = {}
                for ip, expiry in raw.items():
                    out[str(ip)] = None if expiry is None else float(expiry)
                return out
        except Exception as e:
            print(f"{Fore.RED}Chyba při načítání blacklistu:{Style.RESET_ALL} {e}")
    return {}

def save_blacklist(blacklist):
    temp_file = BLACKLIST_FILE + '.tmp'
    try:
        with open(temp_file, 'w') as f:
            json.dump(dict(blacklist), f, indent=4)
            f.flush()
            os.fsync(f.fileno())
        os.replace(temp_file, BLACKLIST_FILE)
    except Exception as e:
        print(f"{Fore.RED}Chyba při ukládání blacklistu:{Style.RESET_ALL} {e}")
        if os.path.exists(temp_file):
            os.remove(temp_file)

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
            if save_wallets:
                save_wallets_enc(wallets, password)
            save_mempool(droid_chain.unconfirmed_transactions)
            save_peers(peers)
            if full or save_wallets:
                print(f"{Fore.GREEN}Data byla úspěšně uložena.{Style.RESET_ALL}")
    except Exception as e:
        print(f"{Fore.RED}Chyba při ukládání dat:{Style.RESET_ALL} {e}")

# OPRAVA #5: Argon2id (64 MiB, 3 iterace, 4 lanes) se počítal při KAŽDÉM
# volání save_wallets_enc, tedy i při každém bloku přijatém ze sítě - 0,385 s
# a 64 MiB špička na rychlém x86, na ARM v Termuxu odhadem 1-3 s. Klíč se nově
# odvodí jednou a drží se v paměti; sůl zůstává stejná jako v souboru, nonce
# je pokaždé nový, takže AES-GCM zůstává bezpečné (dvojice klíč+nonce se nikdy
# neopakuje).
_wallet_key_cache = {'salt': None, 'key': None}

def derive_wallet_key(password, salt=None):
    global _wallet_key_cache
    if salt is None:
        if _wallet_key_cache['key'] is not None and _wallet_key_cache['salt'] is not None:
            return _wallet_key_cache['salt'], _wallet_key_cache['key']
        salt = os.urandom(16)
    elif _wallet_key_cache['salt'] == salt and _wallet_key_cache['key'] is not None:
        return salt, _wallet_key_cache['key']
    kdf = Argon2id(
        salt=salt,
        length=32,
        iterations=3,
        lanes=4,
        memory_cost=65536
    )
    key = kdf.derive(password.encode())
    _wallet_key_cache = {'salt': salt, 'key': key}
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

def save_mempool(unconfirmed_transactions):
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
        c.execute('DELETE FROM transactions')
        for tx in unconfirmed_transactions:
            c.execute('''
                INSERT INTO transactions (tx_id, from_address, to_address, amount, fee, nonce, timestamp, public_key, signature, data, chain_id, mempool_deadline)
                VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
            ''', (tx.tx_id, tx.from_address, tx.to_address, tx.amount, tx.fee, tx.nonce, tx.timestamp, tx.public_key, tx.signature, tx.data, tx.chain_id,
                  getattr(tx, 'mempool_deadline', tx.timestamp + MEMPOOL_TX_EXPIRATION)))
        conn.commit()
        conn.close()
    except Exception as e:
        print(f"{Fore.RED}Chyba při ukládání mempoolu:{Style.RESET_ALL} {e}")

def save_peers(peers):
    temp_file = PEERS_FILE + '.tmp'
    try:
        with open(temp_file, 'w') as f:
            json.dump(peers, f, indent=4)
            f.flush()
            os.fsync(f.fileno())
        os.replace(temp_file, PEERS_FILE)
    except Exception as e:
        print(f"{Fore.RED}Chyba při ukládání peers:{Style.RESET_ALL} {e}")
        if os.path.exists(temp_file):
            os.remove(temp_file)

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
        except Exception as e:
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
                peers = [tuple(p) for p in peers_data]
                print(f"{Fore.GREEN}Peers byly načteny ze souboru.{Style.RESET_ALL}")
        except Exception as e:
            print(f"{Fore.RED}Chyba při načítání peers:{Style.RESET_ALL} {e}")
            
    droid_chain = Blockchain(create_genesis=False)
    
    if os.path.exists(BLOCKCHAIN_DB):
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
            rows = c.fetchall()
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
            }) for row in rows]
            conn.close()
            print(f"{Fore.GREEN}Blockchain byl načten z databáze.{Style.RESET_ALL}")
        except Exception as e:
            print(f"{Fore.RED}Chyba při načítání blockchainu:{Style.RESET_ALL} {e}")
            print(f"{Fore.YELLOW}Vytvářím nový blockchain s genesis blokem.{Style.RESET_ALL}")
            droid_chain.create_genesis_block()
            save_data(droid_chain, wallets, password, peers, full=True, save_wallets=True)
    else:
        print(f"{Fore.YELLOW}Databáze blockchainu nenalezena. Vytvářím nový blockchain s genesis blokem.{Style.RESET_ALL}")
        droid_chain.create_genesis_block()
        save_data(droid_chain, wallets, password, peers, full=True, save_wallets=True)
        
    print(f"{Fore.YELLOW}Provádím plnou validaci blockchain.db při startu...{Style.RESET_ALL}")
    is_valid, chain_state = droid_chain.is_valid_chain()
    if not is_valid:
        print(f"{Fore.RED}CHYBA: Blockchain v blockchain.db je neplatný nebo byl ručně podvržen!{Style.RESET_ALL}")
        print(f"{Fore.RED}Program se ukončuje pro ochranu integrity sítě.{Style.RESET_ALL}")
        sys.exit(1)
        
    droid_chain.balance_map = chain_state['balance_map']
    droid_chain.nonce_map = chain_state['nonce_map']
    droid_chain.total_supply = chain_state['total_supply']
    droid_chain.cumulative_work = chain_state['cumulative_work']
    droid_chain.immature_rewards = chain_state.get('immature_rewards', {})

    # is_valid_chain() nyní v rámci téhož průchodu řetězcem rovnou staví i
    # undo_logs a state_checkpoints (dříve to vyžadovalo druhý, samostatný
    # průchod přes rebuild_state()/update_state_with_block() po validaci).
    # Tím se sloučily dva průchody řetězcem do jednoho a ušetří se CPU čas
    # potřebný na start uzlu.
    droid_chain.undo_logs = chain_state.get('undo_logs', {})
    droid_chain.state_checkpoints = chain_state.get('state_checkpoints', {})

    print(f"{Fore.GREEN}Blockchain validován úspěšně.{Style.RESET_ALL}")
    droid_chain.unconfirmed_transactions = load_mempool(droid_chain)
    return droid_chain, wallets, peers, password

def load_mempool(droid_chain):
    if os.path.exists(MEMPOOL_DB):
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
            ensure_column(conn, 'transactions', 'mempool_deadline', 'INTEGER')
            c.execute("SELECT tx_id, from_address, to_address, amount, fee, nonce, timestamp, public_key, signature, data, chain_id, mempool_deadline FROM transactions")
            rows = c.fetchall()
            conn.close()
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
                    print(f"{Fore.RED}Přeskakuji neplatnou transakci z mempoolu DB (tx_id={row[0]}): {e}{Style.RESET_ALL}")
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
                if not droid_chain.add_transaction(tx, allow_expired=allow_expired):
                    print(f"{Fore.RED}Transakce z mempoolu DB zamítnuta (duplicitní nebo neplatná): {tx.tx_id}{Style.RESET_ALL}")
        except Exception as e:
            print(f"{Fore.RED}Chyba při načítání mempoolu:{Style.RESET_ALL} {e}")
    return droid_chain.unconfirmed_transactions

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
        try:
            while self.alive and self.node.running:
                raw = P2PNode._recv_exactly(self.sock, 4)
                if not raw:
                    break
                msglen = struct.unpack('!I', raw)[0]
                if msglen > MAX_MESSAGE_SIZE:
                    self.node.add_log(f"{Fore.RED}Odpověď od {self.peer} překračuje MAX_MESSAGE_SIZE. Zavírám spojení.{Style.RESET_ALL}")
                    break
                body = P2PNode._recv_exactly(self.sock, msglen)
                if body is None:
                    break
                if not P2PNode._json_depth_ok(body):
                    self.node.add_log(f"{Fore.RED}Odpověď od {self.peer} má příliš hluboké vnoření. Zavírám spojení.{Style.RESET_ALL}")
                    break
                try:
                    message = json.loads(body.decode('utf-8'))
                except (json.JSONDecodeError, UnicodeDecodeError):
                    break
                if not isinstance(message, dict):
                    continue

                rid = message.get('request_id')
                waiter = None
                if rid is not None:
                    with self.pending_lock:
                        waiter = self.pending.pop(rid, None)
                if waiter is not None:
                    waiter.put(message)
                else:
                    # Nevyžádaná zpráva na našem odchozím socketu. Peera jsme
                    # dialovali sami, takže bránu z opravy #10 projde.
                    self.node.handle_message(message, self.peer, reply=self.send)
        except (OSError, socket.timeout, struct.error):
            pass
        except Exception as e:
            self.node.add_log(f"{Fore.RED}Chyba čtecí smyčky spojení s {self.peer}: {e}{Style.RESET_ALL}")
        finally:
            self.close()

    def send(self, message):
        if not self.alive:
            return False
        try:
            with self.send_lock:
                self.sock.sendall(P2PNode._frame(message))
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
        self.peers = initial_peers
        self.peers_lock = threading.Lock()
        self.peer_listen_ports = {self.normalize_ip(ip): port for ip, port in initial_peers}
        self.server_thread = threading.Thread(target=self.start_server)
        self.running = True
        self.bind_ready = threading.Event()
        self.sync_thread = threading.Thread(target=self.sync_chain_periodically)
        self.sync_thread.daemon = True
        self.p2p_log = queue.Queue()
        # OPRAVA #1: token buckets místo seznamu časových razítek.
        # rate_buckets   = levné zprávy / navazovaná spojení
        # expensive_buckets = drahé dotazy (request_blocks, request_full_chain, ...)
        # rate_overflow  = počítadlo dlouhodobého překračování, teprve to vede na ban
        # ETAPA 1: pool perzistentních odchozích spojení a čítač request_id.
        self.connections = {}
        self.connections_lock = threading.Lock()
        self.request_counter = itertools.count(1)
        self.request_counter_lock = threading.Lock()

        self.rate_lock = threading.Lock()
        self.conn_buckets = {}
        self.expensive_byte_buckets = {}
        self.rate_buckets = {}
        self.expensive_buckets = {}
        self.rate_overflow = {}
        self.blacklist_lock = threading.Lock()
        self.blacklist = load_blacklist()
        self.tx_rate_limit = defaultdict(list)
        self.awaiting_full_chain = False
        self.syncing_fork = False
        # ETAPA 3: stahování jednoho forku je vázané na JEDEN uzel. Míchání
        # zdrojů znamená, že nelze určit, kdo dodal vadný blok, a hlavně vede
        # na banování poctivých uzlů - viz komentář v _store_fork_batch().
        self.fork_peer_ip = None
        self.fork_start_index = None
        self.fork_sync_start = 0
        self.SYNC_BUFFER_DB = 'sync_buffer.db'

    def get_locator_hashes(self):
        # OPRAVA #9: dřív se posílalo až LAST_BLOCKS_TO_KEEP (1200) po sobě
        # jdoucích hashů. Protokol z nich stejně použije jen první, který
        # protistrana zná, takže stačí exponenciálně řídnoucí posloupnost:
        # posledních 10 bloků po jednom, pak krok 2, 4, 8, ... To pokryje
        # stejnou hloubku ~32 hashi místo 1200.
        locator = []
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
            conn.close()
        except Exception:
            pass
        return locator

    def init_sync_buffer(self, reset=True):
        # OPRAVA #6c: DROP TABLE se nově dělá jen když opravdu začínáme nový
        # fork (reset=True). Při navazování na rozpracovaný buffer se tabulka
        # zachová, jinak by každý pokus začínal od nuly a hluboký reorg by se
        # nad hraničním RTT nedotáhl nikdy.
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
        conn.close()

    def sync_buffer_tip(self):
        # OPRAVA #6c: (index, hash) posledního bloku v bufferu, nebo None.
        # Používá se k navázání po timeoutu, aby se přenesený pokrok neztratil.
        try:
            if not os.path.exists(self.SYNC_BUFFER_DB):
                return None
            conn = sqlite3.connect(self.SYNC_BUFFER_DB, timeout=1.0)
            c = conn.cursor()
            c.execute("SELECT block_index, block_hash FROM sync_blocks ORDER BY block_index DESC LIMIT 1")
            row = c.fetchone()
            conn.close()
            if row:
                return (row[0], row[1])
        except Exception:
            pass
        return None

    def discard_sync_buffer(self):
        for suffix in ('', '-wal', '-shm'):
            try:
                path = self.SYNC_BUFFER_DB + suffix
                if os.path.exists(path):
                    os.remove(path)
            except OSError:
                pass

    def process_sync_buffer(self):
        self.add_log(f"{Fore.YELLOW}Stahování forku do bufferu dokončeno, spouštím replace_chain()...{Style.RESET_ALL}")
        
        try:
            conn = sqlite3.connect(self.SYNC_BUFFER_DB, timeout=1.0)
            conn.execute("PRAGMA journal_mode=WAL;")
            c = conn.cursor()
            c.execute("SELECT block_index, timestamp, transactions, previous_hash, target_hex, nonce, block_hash, merkle_root, version, chain_id, state_root FROM sync_blocks ORDER BY block_index")
            
            blocks_data = []
            for row in c:
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
            conn.close()
        except Exception as e:
            self.add_log(f"{Fore.RED}Chyba při čtení ze sync bufferu: {e}{Style.RESET_ALL}")
            self.syncing_fork = False
            self.fork_sync_start = 0
            return

        fork_idx = self.fork_start_index
        fork_peer_ip = self.fork_peer_ip
        
        self.syncing_fork = False
        self.fork_start_index = None
        self.fork_sync_start = 0
        self.fork_peer_ip = None
        
        if not blocks_data:
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
        if blocks_data[0]['index'] != fork_idx:
            self.add_log(f"{Fore.YELLOW}Buffer nezačíná na očekávaném indexu #{fork_idx} (má #{blocks_data[0]['index']}). Zahazuji bez postihu.{Style.RESET_ALL}")
            self.discard_sync_buffer()
            return

        for i in range(1, len(blocks_data)):
            if blocks_data[i]['index'] != blocks_data[i-1]['index'] + 1:
                self.add_log(f"{Fore.YELLOW}Díra v bufferu mezi #{blocks_data[i-1]['index']} a #{blocks_data[i]['index']} (chybí odpověď). Zahazuji bez postihu.{Style.RESET_ALL}")
                self.discard_sync_buffer()
                return
            if blocks_data[i]['previous_hash'] != blocks_data[i-1]['hash']:
                self.add_log(f"{Fore.RED}Rozpor v bufferu u bloku #{blocks_data[i]['index']}: previous_hash neodpovídá předchozímu bloku.{Style.RESET_ALL}")
                if fork_peer_ip:
                    self.ban_peer(fork_peer_ip, "nesouvislý řetězec dodaný při fork syncu", BAN_DURATION_PROTOCOL)
                self.discard_sync_buffer()
                return

        global wallets, password
        if self.blockchain.replace_chain(fork_idx, blocks_data):
            save_data(self.blockchain, wallets, password, self.peers)
            self.add_log(f"{Fore.GREEN}Úspěšný reorg z bufferu! (zpracováno {len(blocks_data)} bloků){Style.RESET_ALL}")
        else:
            self.add_log(f"{Fore.RED}Navrhovaný fork z bufferu není platný nebo nemá větší váhu. Odmítnuto.{Style.RESET_ALL}")
            
        # Fork je dotažený (ať už přijatý, nebo odmítnutý) - buffer už nemá smysl.
        self.discard_sync_buffer()

    @staticmethod
    def normalize_ip(ip_str):
        try:
            return str(ipaddress.ip_address(ip_str))
        except ValueError:
            return ip_str

    def add_log(self, message):
        self.p2p_log.put(message)

    def ban_peer(self, ip, reason, duration=BAN_DURATION_SECONDS):
        # OPRAVA #1: jediné místo, kudy se uděluje ban, a je vždy DOČASNÝ.
        # duration=None znamená trvalý ban - ten smí udělit jen uživatel z menu.
        if not ip:
            return
        expiry = None if duration is None else time.time() + duration
        with self.blacklist_lock:
            existing = self.blacklist.get(ip, 0)
            if ip in self.blacklist and existing is None:
                return  # trvalý ban dočasným nepřepisujeme
            self.blacklist[ip] = expiry
            snapshot = dict(self.blacklist)
        save_blacklist(snapshot)
        if expiry is None:
            self.add_log(f"{Fore.RED}Uzel {ip} trvale zablokován. Důvod: {reason}.{Style.RESET_ALL}")
        else:
            self.add_log(f"{Fore.RED}Uzel {ip} dočasně zablokován na {int(duration)} s. Důvod: {reason}.{Style.RESET_ALL}")

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
        ip = addr[0]
        now = time.time()
        with self.rate_lock:
            if len(self.rate_buckets) > 1000:
                self.rate_buckets = {k: v for k, v in self.rate_buckets.items() if now - v[1] < 60}
                self.expensive_buckets = {k: v for k, v in self.expensive_buckets.items() if now - v[1] < 300}
                self.rate_overflow = {k: v for k, v in self.rate_overflow.items() if now - v[1] < 300}

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
        ip = addr[0]
        now = time.time()
        with self.rate_lock:
            if len(self.conn_buckets) > 1000:
                self.conn_buckets = {k: v for k, v in self.conn_buckets.items() if now - v[1] < 300}
            if self._take_token(self.conn_buckets, ip, CONN_BUCKET_CAPACITY, CONN_REFILL_PER_SECOND, now):
                return False
        return True

    def charge_expensive_bytes(self, addr, nbytes):
        # ETAPA 2: bajtový rozpočet pro drahé odpovědi. Počet požadavků je
        # špatná jednotka - request_blocks nad prázdnými bloky stojí zlomek
        # toho, co nad plnými, a strop 1 req/s zastropoval propustnost na
        # 100 bloků/s bez ohledu na hloubku pipeliningu. Bajtový kbelík škáluje
        # se skutečnou prací. Vrací False, když rozpočet nestačí.
        if not addr:
            return True
        ip = addr[0]
        now = time.time()
        with self.rate_lock:
            if len(self.expensive_byte_buckets) > 1000:
                self.expensive_byte_buckets = {k: v for k, v in self.expensive_byte_buckets.items() if now - v[1] < 300}
            tokens, last = self.expensive_byte_buckets.get(ip, (float(EXPENSIVE_BYTES_CAPACITY), now))
            tokens = min(float(EXPENSIVE_BYTES_CAPACITY), tokens + (now - last) * EXPENSIVE_BYTES_PER_SECOND)
            if tokens < nbytes:
                self.expensive_byte_buckets[ip] = (tokens, now)
                return False
            self.expensive_byte_buckets[ip] = (tokens - nbytes, now)
            return True

    def is_expensive_rate_limited(self, addr):
        # OPRAVA #1 + #9: samostatný, mnohem přísnější rozpočet pro dotazy, které
        # čtou z databáze a generují velké odpovědi.
        if not addr:
            return False
        now = time.time()
        with self.rate_lock:
            return not self._take_token(self.expensive_buckets, addr[0], EXPENSIVE_BUCKET_CAPACITY, EXPENSIVE_REFILL_PER_SECOND, now)

    def is_blacklisted(self, addr):
        ip = addr[0] if isinstance(addr, (tuple, list)) else addr
        with self.blacklist_lock:
            if ip not in self.blacklist:
                return False
            expiry = self.blacklist[ip]
            if expiry is None:
                return True
            if time.time() >= expiry:
                # OPRAVA #1: ban vypršel, IP se sama uvolní.
                del self.blacklist[ip]
                snapshot = dict(self.blacklist)
                changed = True
            else:
                return True
        if changed:
            save_blacklist(snapshot)
            self.add_log(f"{Fore.GREEN}Dočasný ban IP {ip} vypršel, uzel je opět povolen.{Style.RESET_ALL}")
        return False

    def is_peer_valid(self, peer_addr):
        if len(self.peers) >= MAX_PEERS:
            return False
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
        while self.running:
            try:
                readable, _, _ = select.select(sockets, [], [], 1.0)
                for s in readable:
                    conn, addr = s.accept()
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
                    client_thread = threading.Thread(target=self.handle_client_connection, args=(conn, addr))
                    client_thread.daemon = True
                    client_thread.start()
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
    def _recv_exactly(conn, n):
        buf = b''
        while len(buf) < n:
            part = conn.recv(n - len(buf))
            if not part:
                return None
            buf += part
        return buf

    @staticmethod
    def _json_depth_ok(data_buffer, max_depth=20):
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

    def handle_client_connection(self, conn, addr):
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
            try:
                with send_lock:
                    conn.sendall(self._frame(message))
                return True
            except (OSError, socket.timeout):
                return False

        with conn:
            conn.settimeout(CONNECTION_IDLE_TIMEOUT)
            unauthenticated_in_row = 0
            try:
                while self.running:
                    raw_msglen = self._recv_exactly(conn, 4)
                    if not raw_msglen:
                        # Peer korektně zavřel spojení - běžný konec, ne chyba.
                        return
                    msglen = struct.unpack('!I', raw_msglen)[0]
                    if msglen > MAX_MESSAGE_SIZE:
                        self.add_log(f"{Fore.RED}Přijatá zpráva příliš velká od {addr}: {msglen} bajtů. Odmítnuto.{Style.RESET_ALL}")
                        self.ban_peer(addr[0], "zpráva překračující MAX_MESSAGE_SIZE")
                        return

                    # ETAPA 2: jeden token za zprávu.
                    if self.is_rate_limited(addr):
                        self.add_log(f"{Fore.YELLOW}Zpráva od {addr} zahozena: vyčerpán limit zpráv.{Style.RESET_ALL}")
                        return

                    data_buffer = self._recv_exactly(conn, msglen)
                    if data_buffer is None:
                        self.add_log(f"{Fore.RED}Spojení s {addr} přerušeno při přijímání dat.{Style.RESET_ALL}")
                        return

                    if not self._json_depth_ok(data_buffer):
                        self.add_log(f"{Fore.RED}Přijatá zpráva má příliš hluboké vnoření. Odmítnuto.{Style.RESET_ALL}")
                        self.ban_peer(addr[0], "příliš hluboce vnořený JSON")
                        return

                    try:
                        message = json.loads(data_buffer.decode('utf-8'))
                    except (json.JSONDecodeError, UnicodeDecodeError) as e:
                        self.add_log(f"{Fore.RED}Chyba dekódování JSON od {addr}: {e}{Style.RESET_ALL}")
                        return

                    accepted = self.handle_message(message, addr, reply=reply)
                    # ETAPA 2: s perzistentním spojením může neznámý uzel držet
                    # socket otevřený donekonečna a posílat zprávy, které se
                    # všechny zahodí branou z opravy #10 - a stojí nás to vlákno.
                    # Po několika odmítnutích za sebou spojení zavřeme.
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
        while self.running and rounds < max_rounds:
            rounds += 1
            tip = self.sync_buffer_tip() if getattr(self, 'syncing_fork', False) else None
            if tip:
                req = {'type': 'request_blocks', 'data': {'locator_hashes': [tip[1]]}}
            else:
                req = {'type': 'request_blocks', 'data': {'locator_hashes': self.get_locator_hashes()}}

            resp = self.send_request(peer, req)
            if resp is None or resp.get('type') != 'response_blocks':
                self.add_log(f"{Fore.YELLOW}Řízený sync s {peer} přerušen (bez odpovědi v kole {rounds}).{Style.RESET_ALL}")
                return False

            self.handle_message(resp, peer, driven=True)

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
        """
        for peer in kandidati:
            if not self.running or getattr(self, 'syncing_fork', False):
                return
            tip = self.sync_buffer_tip()
            if not tip:
                return
            self.add_log(f"{Fore.CYAN}Zkouším obnovit fork sync přes {peer} od #{tip[0]}.{Style.RESET_ALL}")
            if self.sync_blocks_from_peer(peer):
                return
        self.add_log(f"{Fore.YELLOW}Žádný uzel nedodal pokračování forku. Buffer zůstává pro další pokus.{Style.RESET_ALL}")

    def sync_with_peer(self, peer):
        """ETAPA 1: jedno kolo periodické synchronizace s jedním uzlem."""
        resp = self.send_request(peer, {'type': 'request_chain_info'}, timeout=8.0)
        if resp is None:
            # Buď je uzel nedostupný, nebo běží bez téhle změny a odpověděl
            # novým spojením - v tom případě ji zpracovalo handle_message()
            # reaktivně a my tu nemáme co dělat.
            return
        self.handle_message(resp, peer, driven=True)

        mresp = self.send_request(peer, {'type': 'request_mempool'}, timeout=8.0)
        if mresp is not None:
            self.handle_message(mresp, peer, driven=True)

    def _abort_fork_sync(self, addr, reason):
        # Společný úklid při zamítnuté dávce. Buffer se maže, protože dávka byla
        # prokazatelně vadná - navazovat na ni nemá smysl (na rozdíl od timeoutu,
        # kde je buffer v pořádku a jen se přestalo odpovídat, viz OPRAVA #6c).
        self.add_log(f"{Fore.RED}DoS ochrana: {reason} Uzel ignoruji.{Style.RESET_ALL}")
        if addr:
            self.ban_peer(addr[0], reason, BAN_DURATION_PROTOCOL)
        self.syncing_fork = False
        self.fork_start_index = None
        self.fork_sync_start = 0
        self.fork_peer_ip = None
        self.discard_sync_buffer()

    def _store_fork_batch(self, blocks_data, first_block_index, last_block_data, addr, ip_port, has_more, driven=False):
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
        peer_ip = addr[0] if addr else None
        if self.fork_peer_ip is None:
            self.fork_peer_ip = peer_ip
        elif peer_ip != self.fork_peer_ip:
            self.add_log(f"{Fore.YELLOW}Dávka od {ip_port} ignorována: fork se stahuje z {self.fork_peer_ip}. Žádný postih.{Style.RESET_ALL}")
            return

        tip = self.sync_buffer_tip()

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
            try:
                target_val = int(bd['target'], 16) if isinstance(bd['target'], str) else int(bd['target'])
            except (TypeError, ValueError):
                self._abort_fork_sync(addr, f"Blok #{bd.get('index')} má nečitelný target.")
                return

            if target_val <= 0 or target_val > FIXED_TARGET:
                self._abort_fork_sync(addr, f"Blok #{bd.get('index')} deklaruje target mimo povolený rozsah (snazší než síťové minimum).")
                return

            if not Blockchain.meets_difficulty(bd['hash'], target_val):
                self._abort_fork_sync(addr, f"Blok #{bd.get('index')} nesplňuje deklarovaný target.")
                return

            # Nesoulad UVNITŘ dávky je prokazatelná vina odesílatele - ban zůstává.
            if i > 0:
                if bd['previous_hash'] != blocks_data[i-1]['hash'] or bd['index'] != blocks_data[i-1]['index'] + 1:
                    self._abort_fork_sync(addr, "Bloky v dávce nenavazují.")
                    return

        conn = sqlite3.connect(self.SYNC_BUFFER_DB, timeout=1.0)
        conn.execute("PRAGMA journal_mode=WAL;")
        c = conn.cursor()
        for bd in blocks_data:
            tx_json = json.dumps(bd['transactions'])
            c.execute('''
                INSERT OR REPLACE INTO sync_blocks 
                (block_index, timestamp, transactions, previous_hash, target_hex, nonce, block_hash, merkle_root, version, chain_id, state_root)
                VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
            ''', (bd['index'], bd['timestamp'], tx_json, bd['previous_hash'], bd['target'], bd['nonce'], bd['hash'], bd['merkle_root'], bd.get('version', BLOCK_VERSION), bd.get('chain_id', CHAIN_ID), bd.get('state_root')))
        conn.commit()
        conn.close()

        # OPRAVA #6c: watchdog na NEČINNOST - lhůta se obnovuje při každém
        # úspěšném zápisu do bufferu, ne jen jednou na začátku stahování.
        self.fork_sync_start = time.time()

        self.add_log(f"{Fore.CYAN}Uloženo {len(blocks_data)} bloků do bufferu (od #{first_block_index} do #{last_block_data['index']}).{Style.RESET_ALL}")

        # OPRAVA #21: pokračování se řídí příznakem od protistrany, ne délkou
        # dávky - ta může být kratší i kvůli bajtovému stropu.
        if has_more and driven:
            # ETAPA 1: navazující dotaz vydá řídicí smyčka sync_blocks_from_peer(),
            # ne handler - jinak by šly dva dotazy na tutéž dávku.
            return
        if has_more:
            request = {'type': 'request_blocks', 'data': {'locator_hashes': [last_block_data['hash']]}}
            requester_addr = self.resolve_peer_addr(addr)
            if requester_addr:
                self.send_to_peer(requester_addr, request)
            else:
                self.add_log(f"{Fore.YELLOW}Navazující žádost o bloky zahozena: naslouchací port uzlu {ip_port} není znám.{Style.RESET_ALL}")
        else:
            self.process_sync_buffer()

    def resolve_peer_addr(self, addr):
        if not addr:
            return None
        normalized_ip = self.normalize_ip(addr[0])
        with self.peers_lock:
            listen_port = self.peer_listen_ports.get(normalized_ip)
        if listen_port is None:
            return None
        return (addr[0], listen_port)

    def _respond(self, request_msg, response, addr, ip_port, reply, popis):
        """
        ETAPA 1: odpověď se posílá po TOMTÉŽ socketu, na kterém přišel dotaz,
        pokud dotaz nesl request_id. Jinak se padá na starou cestu (nové
        odchozí spojení), takže uzly bez téhle změny fungují dál a
        PROTOCOL_VERSION se zvyšovat nemusí.

        ETAPA 2: velikost odpovědi se účtuje do bajtového rozpočtu peera.
        """
        payload = self._frame(response)
        if not self.charge_expensive_bytes(addr, len(payload) if addr else 0):
            self.add_log(f"{Fore.YELLOW}{popis} od {ip_port} zahozeno: vyčerpán bajtový rozpočet ({len(payload)/1024:.0f} KB).{Style.RESET_ALL}")
            return True

        rid = request_msg.get('request_id')
        if reply is not None and rid is not None:
            response = dict(response)
            response['request_id'] = rid
            if reply(response):
                self.add_log(f"{Fore.YELLOW}{popis} od {ip_port}, odpovídám po stejném spojení (request_id {rid}).{Style.RESET_ALL}")
                return True
            self.add_log(f"{Fore.YELLOW}{popis} od {ip_port}: odpověď po spojení selhala, zkouším nové spojení.{Style.RESET_ALL}")

        responder_addr = self.resolve_peer_addr(addr)
        if responder_addr:
            self.add_log(f"{Fore.YELLOW}{popis} od {ip_port}, odesílám unicastem...{Style.RESET_ALL}")
            self.send_to_peer(responder_addr, response)
            return True
        self.add_log(f"{Fore.YELLOW}{popis} od {ip_port} zahozeno: naslouchací port není znám.{Style.RESET_ALL}")
        return True

    def handle_message(self, message, addr=None, reply=None, driven=False):
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
        if msg_type != 'handshake' and self.resolve_peer_addr(addr) is None:
            self.add_log(f"{Fore.YELLOW}Zpráva typu {msg_type} od neznámého uzlu {ip_port} odmítnuta (chybí handshake).{Style.RESET_ALL}")
            return False

        # OPRAVA #1 + #9: drahé dotazy mají vlastní, mnohem přísnější rozpočet.
        if msg_type in ('request_blocks', 'request_full_chain', 'request_mempool', 'request_chain_info'):
            if self.is_expensive_rate_limited(addr):
                self.add_log(f"{Fore.YELLOW}Dotaz {msg_type} od {ip_port} zahozen: vyčerpán limit drahých dotazů.{Style.RESET_ALL}")
                return True

        self.add_log(f"\n{Fore.CYAN}Přijata zpráva typu: {msg_type} od uzlu {ip_port} Čas {formatted_time}{Style.RESET_ALL}")
        
        if msg_type == 'transaction':
            now = time.time()
            if len(self.tx_rate_limit) > 1000:
                self.tx_rate_limit = defaultdict(list, {k: v for k, v in self.tx_rate_limit.items() if v and now - v[-1] < TX_RATE_WINDOW})
            self.tx_rate_limit[addr[0]] = [t for t in self.tx_rate_limit[addr[0]] if now - t < TX_RATE_WINDOW]
            if len(self.tx_rate_limit[addr[0]]) >= TX_RATE_LIMIT:
                self.ban_peer(addr[0], "překročen limit transakcí")
                return
            self.tx_rate_limit[addr[0]].append(now)
            
            tx_data = message['data']
            tx = Transaction.from_dict(tx_data)
            if self.blockchain.add_transaction(tx):
                self.add_log(f"{Fore.GREEN}Přijata a ověřena nová transakce.{Style.RESET_ALL}")
                save_mempool(self.blockchain.unconfirmed_transactions)
            else:
                self.add_log(f"{Fore.RED}Přijatá transakce je neplatná, odmítnuta.{Style.RESET_ALL}")
                
        elif msg_type == 'request_chain_info':
            local_length = self.blockchain.max_block_index + 1
            local_last_hash = self.blockchain.get_last_block().hash
            local_cum_work = self.blockchain.get_cumulative_work()
            response = {'type': 'response_chain_info', 'data': {'length': local_length, 'last_hash': local_last_hash, 'cum_work': local_cum_work}}
            # OPRAVA #9: broadcastový fallback zrušen. Když resolve_peer_addr()
            # vrátí None, jeden paket od neznámé IP vyrobil N odpovědí ven -
            # čistá amplifikace. Po opravě #10 se sem navíc neznámý uzel vůbec
            # nedostane, takže je tahle větev už jen pojistka.
            self._respond(message, response, addr, ip_port, reply, "Požadavek na info o řetězci")
                
        elif msg_type == 'response_chain_info':
            data = message['data']
            remote_length = data.get('length', 0)
            remote_last_hash = data.get('last_hash', "")
            remote_cum_work = data.get('cum_work', 0)
            
            local_length = self.blockchain.max_block_index + 1
            local_last_hash = self.blockchain.get_last_block().hash
            local_cum_work = self.blockchain.get_cumulative_work()
            
            def request_blocks_from_sender():
                requester_addr = self.resolve_peer_addr(addr)
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
            start_index = message['data'].get('start_index', 0)
            if not isinstance(start_index, int) or start_index < 0:
                start_index = 0
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
                        
            # OPRAVA #21: +1 řádek navíc, abychom poznali, že další bloky existují,
            # aniž bychom je posílali.
            c.execute("SELECT block_index, timestamp, transactions, previous_hash, target_hex, nonce, block_hash, merkle_root, version, chain_id, state_root FROM blocks WHERE block_index >= ? ORDER BY block_index LIMIT ?", (start_index, SYNC_BATCH_SIZE + 1))
            rows = c.fetchall()
            blocks_data = []
            batch_bytes = 0
            has_more = False
            for i, row in enumerate(rows):
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
            conn.close()
            
            # OPRAVA #21: 'has_more' je nutné, protože s bajtovým stropem už
            # kratší dávka neznamená "konec řetězce". Bez toho by si příjemce
            # myslel, že je hotovo, a předčasně by spustil process_sync_buffer().
            response = {'type': 'response_blocks', 'data': blocks_data, 'has_more': has_more}
            self._respond(message, response, addr, ip_port, reply,
                          f"Požadavek na bloky ({len(blocks_data)} od #{start_index}, {batch_bytes / 1024:.0f} KB, další: {'ano' if has_more else 'ne'})")
                
        elif msg_type == 'response_blocks':
            blocks_data = message['data']
            # OPRAVA #21: příznak od protistrany je autoritativní. Uzel bez téhle
            # opravy ho neposílá, takže padáme zpět na původní test délky dávky.
            batch_has_more = message.get('has_more')
            if not isinstance(batch_has_more, bool):
                batch_has_more = (len(blocks_data) == SYNC_BATCH_SIZE)
            
            if not blocks_data:
                if getattr(self, 'syncing_fork', False):
                    self.process_sync_buffer()
                return
                
            self.add_log(f"{Fore.YELLOW}Přijaty bloky ({len(blocks_data)}), zpracovávám...{Style.RESET_ALL}")
            
            current_index = self.blockchain.max_block_index + 1
            last_hash = self.blockchain.get_last_block().hash
            first_block_data = blocks_data[0]
            first_block_index = first_block_data['index']
            last_block_data = blocks_data[-1]
            
            if first_block_index == current_index and first_block_data['previous_hash'] == last_hash and not getattr(self, 'syncing_fork', False):
                added = False
                for block_data in blocks_data:
                    block = Block.from_dict(block_data)
                    if block.index != current_index or block.previous_hash != last_hash:
                        self.add_log(f"{Fore.RED}Uvnitř přijatých bloků je chyba návaznosti, přerušuji.{Style.RESET_ALL}")
                        break
                    if self.blockchain.add_block(block, block.hash):
                        current_index += 1
                        last_hash = block.hash
                        added = True
                    else:
                        self.add_log(f"{Fore.RED}Neplatný blok #{block.index}, přerušuji přidávání.{Style.RESET_ALL}")
                        break
                        
                if added:
                    save_data(self.blockchain, wallets, password, self.peers)
                    self.add_log(f"{Fore.GREEN}Nové bloky úspěšně přidány (přímé pokračování).{Style.RESET_ALL}")
                    
                if batch_has_more and not driven:
                    request = {'type': 'request_blocks', 'data': {'locator_hashes': [last_block_data['hash']]}}
                    requester_addr = self.resolve_peer_addr(addr)
                    if requester_addr:
                        self.send_to_peer(requester_addr, request)
                    else:
                        # OPRAVA #9: bez broadcastu.
                        self.add_log(f"{Fore.YELLOW}Navazující žádost o bloky zahozena: naslouchací port uzlu {ip_port} není znám.{Style.RESET_ALL}")

            else:
                if not getattr(self, 'syncing_fork', False):
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
                        return self._store_fork_batch(blocks_data, first_block_index, last_block_data, addr, ip_port, batch_has_more, driven)

                    self.add_log(f"{Fore.YELLOW}Detekován fork (od bloku #{first_block_index}). Zahajuji ukládání do dočasného bufferu...{Style.RESET_ALL}")
                    
                    conn = sqlite3.connect(BLOCKCHAIN_DB, timeout=1.0)
                    conn.execute("PRAGMA journal_mode=WAL;")
                    c = conn.cursor()
                    c.execute("SELECT block_hash FROM blocks WHERE block_index = ?", (first_block_index - 1,))
                    row = c.fetchone()
                    conn.close()
                    
                    if (not row or row[0] != first_block_data['previous_hash']) and first_block_index != 0:
                        if self.blockchain.max_block_index == 0:
                            self.awaiting_full_chain = True
                            request = {'type': 'request_full_chain'}
                            requester_addr = self.resolve_peer_addr(addr)
                            if requester_addr:
                                self.add_log(f"{Fore.RED}Nedokážu navázat přijaté bloky. Fallback na full sync...{Style.RESET_ALL}")
                                self.send_to_peer(requester_addr, request)
                            else:
                                # OPRAVA #9: bez broadcastu; navíc bychom jinak
                                # nechali awaiting_full_chain zbytečně otevřený.
                                self.awaiting_full_chain = False
                                self.add_log(f"{Fore.YELLOW}Fallback na full sync zrušen: naslouchací port uzlu {ip_port} není znám.{Style.RESET_ALL}")
                            return
                        else:
                            self.add_log(f"{Fore.RED}Varování: Detekován pokus o hluboký reorg / long-range útok. Fallback na fullsync zamítnut.{Style.RESET_ALL}")
                            if addr:
                                self.ban_peer(addr[0], "pokus o hluboký reorg / long-range útok", BAN_DURATION_PROTOCOL)
                            self.syncing_fork = False
                            self.fork_start_index = None
                            self.fork_sync_start = 0
                            return

                    # Nový fork - buffer po případném starém pokusu zahodíme.
                    self.discard_sync_buffer()
                    self.syncing_fork = True
                    self.fork_start_index = first_block_index
                    self.fork_sync_start = time.time()
                    self.fork_peer_ip = addr[0] if addr else None
                    self.init_sync_buffer(reset=True)

                return self._store_fork_batch(blocks_data, first_block_index, last_block_data, addr, ip_port, batch_has_more, driven)

        elif msg_type == 'request_full_chain':
            conn = sqlite3.connect(BLOCKCHAIN_DB, timeout=1.0)
            conn.execute("PRAGMA journal_mode=WAL;")
            c = conn.cursor()
            # OPRAVA #21: stejný bajtový strop jako u request_blocks - i tady by
            # 100 plných bloků přeteklo MAX_MESSAGE_SIZE a vedlo na ban poctivého uzlu.
            c.execute("SELECT block_index, timestamp, transactions, previous_hash, target_hex, nonce, block_hash, merkle_root, version, chain_id, state_root FROM blocks ORDER BY block_index LIMIT ?", (SYNC_BATCH_SIZE,))
            chain_data = []
            full_chain_bytes = 0
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
            conn.close()
            response = {'type': 'response_full_chain', 'data': chain_data}
            # OPRAVA #9: broadcast fallback zrušen i tady - tahle odpověď je ze
            # všech nejdražší.
            self._respond(message, response, addr, ip_port, reply,
                          f"Požadavek na full-chain ({len(chain_data)} bloků)")
                
        elif msg_type == 'response_full_chain':
            if not getattr(self, 'awaiting_full_chain', False):
                self.add_log(f"{Fore.YELLOW}Přijat nevyžádaný response_full_chain od uzlu {ip_port}, ignoruji.{Style.RESET_ALL}")
                return
            self.awaiting_full_chain = False
            new_chain_data = message.get('data', [])
            
            if self.blockchain.replace_chain(0, new_chain_data):
                save_data(self.blockchain, wallets, password, self.peers)
                self.add_log(f"{Fore.GREEN}Počáteční dávka blockchainu z reorgu (od indexu 0) byla úspěšně uložena. Zbytek stáhne inkrementální proces.{Style.RESET_ALL}")
            else:
                self.add_log(f"{Fore.YELLOW}Přijatý počáteční řetězec není platný nebo lepší, odmítám ho.{Style.RESET_ALL}")
                
        elif msg_type == 'new_block':
            new_block_data = message['data']
            new_block = Block.from_dict(new_block_data)
            
            # Rychlá validace PoW před složitějším zpracováním
            quick_hash = new_block.compute_hash()
            if quick_hash != new_block.hash or not Blockchain.meets_difficulty(quick_hash, new_block.target):
                self.add_log(f"{Fore.RED}Přijatý blok neprošel rychlou kontrolou PoW, zahozeno.{Style.RESET_ALL}")
                return
                
            if self.blockchain.add_block(new_block, new_block.hash):
                # Zastavíme těžení až po úspěšném ověření a zapsání bloku do DB uvnitř add_block
                if self.blockchain.mining_in_progress:
                    self.blockchain.mining_in_progress = False
                    self.add_log(f"{Fore.YELLOW}Těžba zastavena, přijat platný nový blok.{Style.RESET_ALL}")
                    
                self.add_log(f"{Fore.GREEN}Přijat a přidán nový blok {new_block.index} od jiného uzlu.{Style.RESET_ALL}")
                self.add_log(f"{Fore.YELLOW}Mempool byl bezpečně aktualizován.{Style.RESET_ALL}")
                save_data(self.blockchain, wallets, password, self.peers)
            else:
                conn = sqlite3.connect(BLOCKCHAIN_DB, timeout=1.0)
                conn.execute("PRAGMA journal_mode=WAL;")
                c = conn.cursor()
                c.execute("SELECT 1 FROM blocks WHERE block_hash = ?", (new_block.previous_hash,))
                exists = c.fetchone() is not None
                conn.close()
                
                if exists:
                    request = {'type': 'request_chain_info'}
                    requester_addr = self.resolve_peer_addr(addr)
                    if requester_addr:
                        self.add_log(f"{Fore.YELLOW}Přijatý blok není navázaný na náš poslední blok. Zahajuji synchronizaci s {ip_port}...{Style.RESET_ALL}")
                        self.send_to_peer(requester_addr, request)
                    else:
                        self.add_log(f"{Fore.YELLOW}Přijatý blok není navázaný na náš poslední blok, ale naslouchací port uzlu {ip_port} není znám. Ignoruji.{Style.RESET_ALL}")
                else:
                    self.blockchain.add_orphan_block(new_block)
                    self.add_log(f"{Fore.YELLOW}Přijat orphan blok {new_block.index}, uložen do poolu.{Style.RESET_ALL}")
                    
        elif msg_type == 'request_mempool':
            response = {'type': 'response_mempool', 'data': [tx.to_dict() for tx in self.blockchain.unconfirmed_transactions]}
            self._respond(message, response, addr, ip_port, reply, "Požadavek na mempool")
                
        elif msg_type == 'response_mempool':
            tx_data_list = message['data']
            self.add_log(f"{Fore.YELLOW}Přijat mempool s {len(tx_data_list)} transakcemi.{Style.RESET_ALL}")
            for tx_data in tx_data_list:
                tx = Transaction.from_dict(tx_data)
                if tx.tx_id not in {t.tx_id for t in self.blockchain.unconfirmed_transactions}:
                    tx_nonce = self.blockchain.get_next_nonce(tx.from_address)
                    if tx.nonce == tx_nonce and self.blockchain.add_transaction(tx):
                        self.add_log(f"{Fore.GREEN}Přidána nová transakce z mempoolu od uzlu: {tx.tx_id}{Style.RESET_ALL}")
                    else:
                        self.add_log(f"{Fore.RED}Transakce z mempoolu zamítnuta (neplatná nonce nebo jiná chyba): {tx.tx_id}{Style.RESET_ALL}")
            save_mempool(self.blockchain.unconfirmed_transactions)
            
        elif msg_type == 'new_peer':
            new_peer_addr = tuple(message['data'])
            try:
                ip = ipaddress.ip_address(new_peer_addr[0])
                is_allowed_ip = not (ip.is_loopback or ip.is_private or ip.is_multicast or ip.is_reserved or ip.is_unspecified)
            except ValueError:
                is_allowed_ip = False
                
            if is_allowed_ip:
                with self.peers_lock:
                    should_connect = new_peer_addr not in self.peers and new_peer_addr != (self.host, self.port) and self.is_peer_valid(new_peer_addr)
                if should_connect:
                    self.connect_to_peer(new_peer_addr)
            else:
                self.add_log(f"{Fore.YELLOW}Zpráva 'new_peer' ignorována: Adresa {new_peer_addr[0]} není povolená veřejná IP.{Style.RESET_ALL}")
                
        elif msg_type == 'handshake':
            remote_protocol_version = message.get('protocol_version')
            remote_software_version = message.get('software_version', 'neznámá')
            remote_chain_id = message.get('chain_id')
            remote_node_id = message.get('node_id')
            
            if remote_node_id and remote_node_id == getattr(self, 'node_id', None):
                self.add_log(f"{Fore.YELLOW}Varování: Detekováno připojení k sobě samému (shoda Node ID)! Spojení zahozeno.{Style.RESET_ALL}")
                if addr:
                    normalized_ip = self.normalize_ip(addr[0])
                    remote_listen_port = message.get('listen_port')
                    if remote_listen_port:
                        peer_to_remove = (addr[0], remote_listen_port)
                        with self.peers_lock:
                            if peer_to_remove in self.peers:
                                self.peers.remove(peer_to_remove)
                            self.peer_listen_ports.pop(normalized_ip, None)
                            peers_snapshot = list(self.peers)
                        save_peers(peers_snapshot)
                return
                
            if remote_chain_id != CHAIN_ID:
                if addr:
                    self.ban_peer(addr[0], f"handshake: cizí chain_id {remote_chain_id}", BAN_DURATION_PROTOCOL)
                self.add_log(f"{Fore.RED}Handshake selhal od uzlu {ip_port}: nesprávné chain_id {remote_chain_id} (očekáváno {CHAIN_ID}). Uzel blacklistován.{Style.RESET_ALL}")
            elif remote_protocol_version != PROTOCOL_VERSION:
                if addr:
                    self.ban_peer(addr[0], f"handshake: nekompatibilní protocol_version {remote_protocol_version}", BAN_DURATION_PROTOCOL)
                self.add_log(f"{Fore.RED}Handshake selhal od uzlu {ip_port}: nekompatibilní protocol_version {remote_protocol_version} (očekáváno {PROTOCOL_VERSION}). Uzel blacklistován.{Style.RESET_ALL}")
            else:
                self.add_log(f"{Fore.GREEN}Handshake úspěšný od uzlu {ip_port}: software_version={remote_software_version}, protocol_version={remote_protocol_version}, chain_id={remote_chain_id}.{Style.RESET_ALL}")
                remote_listen_port = message.get('listen_port')
                if addr and isinstance(remote_listen_port, int) and 0 < remote_listen_port <= 65535:
                    normalized_ip = self.normalize_ip(addr[0])
                    with self.peers_lock:
                        self.peer_listen_ports[normalized_ip] = remote_listen_port
                    new_peer_addr = (addr[0], remote_listen_port)
                    
                    try:
                        ip_obj = ipaddress.ip_address(addr[0])
                        is_allowed_ip = not (ip_obj.is_loopback or ip_obj.is_private or ip_obj.is_multicast or ip_obj.is_reserved or ip_obj.is_unspecified)
                    except ValueError:
                        is_allowed_ip = False
                        
                    if is_allowed_ip and new_peer_addr != (self.host, self.port):
                        changed = False
                        with self.peers_lock:
                            old_peer = None
                            for p in self.peers:
                                if p[0] == addr[0]:
                                    old_peer = p
                                    break
                            
                            if old_peer:
                                if old_peer[1] != remote_listen_port:
                                    self.peers.remove(old_peer)
                                    self.peers.append(new_peer_addr)
                                    changed = True
                            else:
                                if self.is_peer_valid(new_peer_addr):
                                    self.peers.append(new_peer_addr)
                                    changed = True
                            
                            peers_snapshot = list(self.peers)
                            
                        if changed:
                            save_peers(peers_snapshot)
                            self.add_log(f"{Fore.GREEN}Uzel {ip_port} (naslouchá na portu {remote_listen_port}) byl aktualizován/přidán do peers.{Style.RESET_ALL}")

    def connect_to_peer(self, peer_addr):
        if self.is_blacklisted(peer_addr):
            self.add_log(f"{Fore.YELLOW}Spojení zrušeno: Uzel {peer_addr[0]} je na blacklistu.{Style.RESET_ALL}")
            return False
            
        with self.peers_lock:
            already_peer = peer_addr in self.peers
            
        if not already_peer:
            try:
                addr_info = socket.getaddrinfo(peer_addr[0], peer_addr[1], socket.AF_UNSPEC, socket.SOCK_STREAM)
                family, socktype, proto, _, sockaddr = addr_info[0]
                client_socket = socket.socket(family, socktype, proto)
                client_socket.settimeout(3)
                client_socket.connect(sockaddr)
                
                local_ip = client_socket.getsockname()[0]
                if local_ip == peer_addr[0] or peer_addr[0] in ['127.0.0.1', 'localhost', '::1', '0.0.0.0']:
                    self.add_log(f"{Fore.YELLOW}Spojení zrušeno: Pokus o připojení na vlastní IP adresu ({peer_addr[0]}).{Style.RESET_ALL}")
                    client_socket.close()
                    return False
                    
                with self.peers_lock:
                    self.peers.append(peer_addr)
                    self.peer_listen_ports[self.normalize_ip(peer_addr[0])] = peer_addr[1]
                    peers_snapshot = list(self.peers)
                    
                self.add_log(f"{Fore.GREEN}Úspěšně připojeno k uzlu {peer_addr}{Style.RESET_ALL}")

                # OPRAVA #1: dřív tohle spálilo 4 spojení naráz (testovací
                # connect výše + tři samostatné send_to_peer), tedy 40 %
                # původního rozpočtu při jediném připojení. Handshake i oba
                # dotazy teď jdou po JEDNOM socketu - tom, který už máme
                # otevřený a jehož úspěšné navázání bylo celým smyslem testu.
                try:
                    client_socket.sendall(b''.join(self._frame(m) for m in [
                        {'type': 'handshake', 'protocol_version': PROTOCOL_VERSION, 'software_version': SOFTWARE_VERSION,
                         'chain_id': CHAIN_ID, 'listen_port': self.port, 'node_id': getattr(self, 'node_id', 'unknown')},
                        {'type': 'request_chain_info'},
                        {'type': 'request_mempool'},
                    ]))
                finally:
                    client_socket.close()

                save_peers(peers_snapshot)
                return True
            except ConnectionRefusedError:
                peer_str = f"[{peer_addr[0]}]:{peer_addr[1]}" if ':' in peer_addr[0] else f"{peer_addr[0]}:{peer_addr[1]}"
                print(f"{Fore.RED}Chyba:{Style.RESET_ALL} Nelze se připojit k uzlu {peer_str}")
            except Exception as e:
                print(f"{Fore.RED}Chyba při připojování:{Style.RESET_ALL} {e}")
        return False

    def connect_to_all_peers(self):
        with self.peers_lock:
            peers_snapshot = list(self.peers)
        for peer in peers_snapshot:
            self.connect_to_peer(peer)

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
            if all(conn.send(m) for m in messages):
                if hasattr(self, 'offline_peers') and peer in self.offline_peers:
                    self.offline_peers.remove(peer)
                    self.add_log(f"{Fore.GREEN}Uzel {peer_str} je online{Style.RESET_ALL}")
                return

        try:
            addr_info = socket.getaddrinfo(peer[0], peer[1], socket.AF_UNSPEC, socket.SOCK_STREAM)
            family, socktype, proto, _, sockaddr = addr_info[0]
            client_socket = socket.socket(family, socktype, proto)
            client_socket.settimeout(5)
            client_socket.connect(sockaddr)
            
            payload = b''.join(self._frame(m) for m in messages)
            client_socket.sendall(payload)
            client_socket.close()
            
            if hasattr(self, 'offline_peers') and peer in self.offline_peers:
                self.offline_peers.remove(peer)
                self.add_log(f"{Fore.GREEN}Uzel {peer_str} je online{Style.RESET_ALL}")
        except (ConnectionRefusedError, socket.timeout, OSError):
            if not hasattr(self, 'offline_peers'):
                self.offline_peers = set()
            if peer not in self.offline_peers:
                self.offline_peers.add(peer)
                self.add_log(f"{Fore.RED}Uzel {peer_str} je offline{Style.RESET_ALL}")
        except Exception as e:
            self.add_log(f"{Fore.RED}Neočekávaná chyba u uzlu {peer_str} - {e}{Style.RESET_ALL}")

    def send_to_peer(self, peer_addr, data):
        thread = threading.Thread(target=self._send_to_single_peer, args=(peer_addr, data))
        thread.daemon = True
        thread.start()

    def send_data_to_peers(self, data):
        with self.peers_lock:
            peers_snapshot = list(self.peers)
        for peer in peers_snapshot:
            thread = threading.Thread(target=self._send_to_single_peer, args=(peer, data))
            thread.daemon = True
            thread.start()

    def sync_chain_periodically(self):
        while self.running:
            time.sleep(10)
            
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
                    self.fork_peer_ip = None
                    tip = self.sync_buffer_tip()
                    if tip:
                        # ETAPA 3: dřív tu byl BROADCAST všem uzlům. Odpovědělo
                        # jich víc, první posunula špičku bufferu a druhá už na ni
                        # nenavazovala - a poctivý uzel schytal 24hodinový ban.
                        # Obnovení proto vede řízený dialog s JEDNÍM uzlem.
                        self.add_log(f"{Fore.CYAN}V bufferu je {tip[0] - (self.fork_start_index or tip[0]) + 1} bloků (do #{tip[0]}), obnovuji stahování.{Style.RESET_ALL}")
                        with self.peers_lock:
                            kandidati = list(self.peers)
                        if kandidati:
                            t = threading.Thread(target=self._resume_fork_sync, args=(kandidati,))
                            t.daemon = True
                            t.start()
                    else:
                        # Prázdný buffer nemá cenu držet.
                        self.fork_start_index = None
                        self.discard_sync_buffer()
                        
            self.blockchain.cleanup_mempool()
            with self.peers_lock:
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

def show_p2p_log():
    print(f"\n{Fore.YELLOW}--- Log P2P sítě (stiskněte Enter pro návrat) ---{Style.RESET_ALL}")
    while not p2p_node.p2p_log.empty():
        print(p2p_node.p2p_log.get())
    input()

def get_mempool_size_bytes(unconfirmed_transactions):
    return sum(tx.get_size() for tx in unconfirmed_transactions)

def print_menu():
    print(f"\n{Fore.YELLOW}--- Menu ---{Style.RESET_ALL}")
    print(f"{Fore.GREEN}1{Style.RESET_ALL} - Zobrazit peněženky a zůstatky")
    print(f"{Fore.GREEN}2{Style.RESET_ALL} - Vytvořit transakci")
    print(f"{Fore.GREEN}3{Style.RESET_ALL} - Zobrazit nepotvrzené transakce")
    print(f"{Fore.GREEN}4{Style.RESET_ALL} - Vytěžit nový blok")
    print(f"{Fore.GREEN}5{Style.RESET_ALL} - Uložené adresy")
    print(f"{Fore.GREEN}6{Style.RESET_ALL} - Vytvořit novou peněženku")
    print(f"{Fore.GREEN}7{Style.RESET_ALL} - Importovat privátní klíč")
    print(f"{Fore.GREEN}8{Style.RESET_ALL} - Exportovat privátní klíč")
    print(f"{Fore.GREEN}9{Style.RESET_ALL} - Smazat peněženku")
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

def enforce_mobile_environment():
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
    enforce_mobile_environment()
    global wallets
    global p2p_node
    global password
    global read_only
    global address_book
    read_only = False
    
    verify_genesis_address()
    sync_time_with_ntp()
    
    if len(sys.argv) > 1:
        p2p_port = int(sys.argv[1])
    else:
        p2p_port = 5001
        
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
                    for address, wallet in wallets.items():
                        confirmed_balance = droid_chain.get_confirmed_balance(address)
                        pending_outgoing = []
                        pending_incoming = []
                        pending_outgoing_sum = 0
                        
                        for tx in droid_chain.unconfirmed_transactions:
                            if tx.from_address == address:
                                pending_outgoing.append(tx)
                                pending_outgoing_sum += tx.amount + tx.fee
                            if tx.to_address == address:
                                pending_incoming.append(tx)
                                
                        total_balance = confirmed_balance - pending_outgoing_sum
                        pending_incoming_sum = sum(tx.amount for tx in pending_incoming)
                        
                        immature_sum = sum(reward['amount'] for idx, reward in droid_chain.immature_rewards.items() if reward['address'] == address)
                        
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
                                print(f"  --------------------")
                                
                        if pending_incoming:
                            print(f" Pending (+): {Fore.GREEN}+{format(pending_incoming_dec, f'.{DECIMALS}f')} {TICKER}{Style.RESET_ALL}")
                            for tx in pending_incoming:
                                tx_amount_dec = Decimal(tx.amount) / Decimal(10 ** DECIMALS)
                                print(f"  Odesílatel: {tx.from_address}")
                                print(f"  Částka: {Fore.GREEN}+{format(tx_amount_dec, f'.{DECIMALS}f')} {TICKER}{Style.RESET_ALL}")
                                print(f"  Poplatek: {Fore.YELLOW}{format(Decimal(tx.fee) / Decimal(10 ** DECIMALS), f'.{DECIMALS}f')} {TICKER}{Style.RESET_ALL}")
                                print(f"  TX ID: {tx.tx_id}")
                                print(f"  --------------------")
                        print("-" * 40)
                        
            elif choice == "2":
                if not p2p_node.get_online_peers():
                    print(f"{Fore.RED}Chyba:{Style.RESET_ALL} Vytvoření transakce není možné. Musíte být připojen k alespoň jednomu dalšímu uzlu.")
                    continue
                from_address = input(f"Zadejte ADRESU peněženky odesílatele: ").strip()
                if len(from_address) >= 3:
                    from_address = from_address[:3].upper() + from_address[3:].lower()
                if from_address not in wallets:
                    print(f"{Fore.RED}Chyba:{Style.RESET_ALL} Peněženka s adresou '{from_address}' neexistuje. Nejdříve ji vytvořte nebo importujte.")
                    continue
                    
                to_address = input(f"Zadejte ADRESU příjemce: ").strip()
                if len(to_address) >= 3:
                    to_address = to_address[:3].upper() + to_address[3:].lower()
                if not is_valid_address(to_address):
                    print(f"{Fore.RED}Chyba:{Style.RESET_ALL} Neplatný formát adresy příjemce.")
                    continue
                if from_address == to_address:
                    print(f"{Fore.RED}Chyba:{Style.RESET_ALL} Nelze posílat peníze na stejnou adresu.")
                    continue
                    
                amount_str = input(f"Zadejte částku: ").strip()
                amount_str = amount_str.replace(',', '.')
                parts = amount_str.split('.')
                if len(parts) > 2 or not parts[0].isdigit() or (len(parts) == 2 and (not parts[1].isdigit() or len(parts[1]) > DECIMALS)):
                    print(f"{Fore.RED}Chyba:{Style.RESET_ALL} Neplatný formát částky. Povolena jsou pouze čísla (0-9), jedna tečka a max. {DECIMALS} desetinných míst.")
                    continue
                    
                try:
                    amount_decimal = Decimal(amount_str)
                    amount_in_decimal = int(amount_decimal * (10 ** DECIMALS))
                    if amount_in_decimal < MIN_TX_AMOUNT:
                        print(f"{Fore.RED}Chyba:{Style.RESET_ALL} Částka transakce je příliš malá. Minimální částka je {format(MIN_TX_AMOUNT / (10 ** DECIMALS), f'.{DECIMALS}f')} {TICKER}.")
                        continue
                except Exception:
                    print(f"{Fore.RED}Chyba:{Style.RESET_ALL} Částka musí být platné číslo.")
                    continue
                    
                current_available_balance = droid_chain.get_confirmed_balance(from_address)
                for tx_in_mempool in droid_chain.unconfirmed_transactions:
                    if tx_in_mempool.from_address == from_address:
                        current_available_balance -= (tx_in_mempool.amount + tx_in_mempool.fee)
                        
                if current_available_balance < amount_in_decimal + TX_FEE_MIN:
                    print(f"{Fore.RED}Chyba:{Style.RESET_ALL} Nedostatečný zůstatek pro tuto částku (včetně min. poplatku). K dispozici: {format(Decimal(current_available_balance) / Decimal(10**DECIMALS), f'.{DECIMALS}f')} {TICKER}")
                    continue
                    
                fee_str = input(f"Zadejte poplatek ({format(Decimal(TX_FEE_MIN)/(10**DECIMALS), f'.{DECIMALS}f')}-{format(Decimal(TX_FEE_MAX)/(10**DECIMALS), f'.{DECIMALS}f')} {TICKER}, prázdné pro {format(Decimal(TX_FEE_MIN)/(10**DECIMALS), f'.{DECIMALS}f')}): ").strip()
                if fee_str == "":
                    fee = TX_FEE_MIN
                else:
                    fee_str = fee_str.replace(',', '.')
                    parts_fee = fee_str.split('.')
                    if len(parts_fee) > 2 or not parts_fee[0].isdigit() or (len(parts_fee) == 2 and (not parts_fee[1].isdigit() or len(parts_fee[1]) > DECIMALS)):
                        print(f"{Fore.RED}Chyba:{Style.RESET_ALL} Neplatný formát poplatku. Povolena jsou pouze čísla (0-9), jedna tečka a max. {DECIMALS} desetinných míst.")
                        continue
                    try:
                        fee_decimal = Decimal(fee_str)
                        fee = int(fee_decimal * (10 ** DECIMALS))
                        if TX_FEE_MIN > fee or fee > TX_FEE_MAX:
                            print(f"{Fore.RED}Chyba:{Style.RESET_ALL} Poplatek za transakci je mimo povolený rozsah.")
                            continue
                    except Exception:
                        print(f"{Fore.RED}Chyba:{Style.RESET_ALL} Neplatný formát poplatku.")
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
                    
                    if any(t.tx_id == tx.tx_id for t in droid_chain.unconfirmed_transactions):
                        print(f"{Fore.RED}Chyba:{Style.RESET_ALL} Duplicitní TX ID {tx.tx_id} po vytvoření. Transakce odmítnuta.")
                        continue
                    if tx.from_address != "COINBASE" and any(t.nonce == tx.nonce and t.from_address == tx.from_address for t in droid_chain.unconfirmed_transactions):
                        print(f"{Fore.RED}Chyba:{Style.RESET_ALL} Duplicitní nonce {tx.nonce} pro adresu {tx.from_address} po vytvoření. Transakce odmítnuta.")
                        continue
                        
                    if droid_chain.add_transaction(tx):
                        print(f"{Fore.GREEN}Transakce byla úspěšně přidána do fronty.{Style.RESET_ALL}")
                        print(f" TX ID: {Fore.MAGENTA}{tx.tx_id}{Style.RESET_ALL}")
                        print(f" Nonce: {Fore.MAGENTA}{tx.nonce}{Style.RESET_ALL}")
                        print(f"{Fore.GREEN}Transakce byla podepsána privátním klíčem.{Style.RESET_ALL}")
                        save_mempool(droid_chain.unconfirmed_transactions)
                        p2p_node.send_data_to_peers({'type': 'transaction', 'data': tx.to_dict()})
                        
            elif choice == "3":
                print(f"\n{Fore.YELLOW}--- Mempool (nepotvrzené transakce) ---{Style.RESET_ALL}")
                mempool_size_bytes = get_mempool_size_bytes(droid_chain.unconfirmed_transactions)
                mempool_size_kb = mempool_size_bytes / 1024
                mempool_size_mb = mempool_size_kb / 1024
                tx_count = len(droid_chain.unconfirmed_transactions)
                print(f"Velikost mempoolu: {Fore.CYAN}{tx_count} TX / {mempool_size_kb:.2f} KB / {mempool_size_mb:.2f} MB{Style.RESET_ALL}")
                
                if not droid_chain.unconfirmed_transactions:
                    print("    Mempool je prázdný.")
                else:
                    for tx in droid_chain.unconfirmed_transactions:
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
                        save_data(droid_chain, wallets, password, p2p_node.peers)
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
                print(f" {Fore.RED}Informace: Privátní klíč byl bezpečně uložen do souboru.{Style.RESET_ALL}")
                save_data(droid_chain, wallets, password, p2p_node.peers, save_wallets=True)
                
            elif choice == "7":
                key_hex = input(f"Zadejte privátní klíč (hex): ")
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
                save_data(droid_chain, wallets, password, p2p_node.peers, save_wallets=True)
                
            elif choice == "8":
                address = input(f"Zadejte ADRESU peněženky, jejíž klíč chcete exportovat: ")
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
                address_to_delete = input(f"Zadejte ADRESU peněženky, kterou chcete smazat: ")
                if address_to_delete in wallets:
                    confirm = input(f"\n{Fore.YELLOW}Jste si jistí že chcete tuto peněženku smazat? Tato akce je nevratná (a/n): {Style.RESET_ALL}").strip().lower()
                    if confirm == 'a':
                        del wallets[address_to_delete]
                        print(f"\n{Fore.GREEN}Peněženka '{address_to_delete}' byla úspěšně smazána.{Style.RESET_ALL}")
                        save_data(droid_chain, wallets, password, p2p_node.peers, save_wallets=True)
                    else:
                        print(f"\n{Fore.YELLOW}Akce zrušena. Peněženka nebyla smazána.{Style.RESET_ALL}")
                else:
                    print(f"{Fore.RED}Chyba:{Style.RESET_ALL} Peněženka s adresou '{address_to_delete}' neexistuje.")
                    
            elif choice == "10":
                print(f"\n{Fore.YELLOW}--- Blockchain ---{Style.RESET_ALL}")
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
                    print(f" Merkle root: {Fore.CYAN}{block.merkle_root}{Style.RESET_ALL}")
                    print(f" State root: {Fore.CYAN}{block.state_root}{Style.RESET_ALL}")
                    print(f" Cílová obtížnost: {Fore.CYAN}{target_hex}{Style.RESET_ALL}")
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
                
                conn.close()
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
                if search_input.isdigit():
                    try:
                        block_index = int(search_input)
                        if 0 <= block_index <= droid_chain.max_block_index:
                            block = droid_chain.get_block(block_index)
                        else:
                            print(f"{Fore.RED}Blok s číslem {block_index} neexistuje.{Style.RESET_ALL}")
                    except ValueError:
                        print(f"{Fore.RED}Neplatné číslo bloku.{Style.RESET_ALL}")
                else:
                    conn = sqlite3.connect(BLOCKCHAIN_DB, timeout=1.0)
                    conn.execute("PRAGMA journal_mode=WAL;")
                    c = conn.cursor()
                    c.execute("SELECT block_index, timestamp, transactions, previous_hash, target_hex, nonce, block_hash, merkle_root, version, chain_id, state_root FROM blocks WHERE block_hash = ?", (search_input,))
                    row = c.fetchone()
                    conn.close()
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
                    print(f" Merkle root: {Fore.CYAN}{block.merkle_root}{Style.RESET_ALL}")
                    print(f" State root: {Fore.CYAN}{block.state_root}{Style.RESET_ALL}")
                    print(f" Cílová obtížnost: {Fore.CYAN}{target_hex}{Style.RESET_ALL}")
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
                tx_id = input("Zadejte TX ID transakce: ")
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
                address = input(f"Zadejte ADRESU pro zobrazení historie transakcí: ")
                print(f"\n{Fore.YELLOW}--- Historie transakcí pro adresu '{address}' ---{Style.RESET_ALL}")
                sent_amount = 0
                received_amount = 0
                sent_count = 0
                received_count = 0
                tx_list = []
                tx_found = False
                
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
                conn.close()
                
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
                        
                pending_list = [
                    tx for tx in droid_chain.unconfirmed_transactions
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
                        
                confirmed_balance = droid_chain.get_confirmed_balance(address)
                immature_sum = sum(reward['amount'] for idx, reward in droid_chain.immature_rewards.items() if reward['address'] == address)
                total_coins = sent_amount + received_amount
                total_count = sent_count + received_count
                
                confirmed_dec = Decimal(confirmed_balance) / Decimal(10 ** DECIMALS)
                immature_dec = Decimal(immature_sum) / Decimal(10 ** DECIMALS)
                sent_dec = Decimal(sent_amount) / Decimal(10 ** DECIMALS)
                received_dec = Decimal(received_amount) / Decimal(10 ** DECIMALS)
                total_coins_dec = Decimal(total_coins) / Decimal(10 ** DECIMALS)
                
                print(f"\n{Fore.YELLOW}--- Statistiky historie transakcí ---{Style.RESET_ALL}")
                print(f"Potvrzený zůstatek: {Fore.MAGENTA}{format(confirmed_dec, f'.{DECIMALS}f')} {TICKER}{Style.RESET_ALL}")
                print(f"Nepotvrzený zůstatek: {Fore.BLUE}{format(immature_dec, f'.{DECIMALS}f')} {TICKER}{Style.RESET_ALL}")
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
                miner_addr = input(f"Zadejte ADRESU těžaře pro zobrazení coinbase odměn: ").strip()
                if miner_addr:
                    if not is_valid_address(miner_addr):
                        print(f"{Fore.RED}Chyba: Neplatný formát adresy.{Style.RESET_ALL}")
                    else:
                        print(f"\n{Fore.YELLOW}--- Historie coinbase odměn pro adresu '{miner_addr}' ---{Style.RESET_ALL}")
                        locked_rewards_count = 0
                        unlocked_rewards_count = 0
                        locked_coins = 0
                        unlocked_coins = 0
                        
                        conn = sqlite3.connect(BLOCKCHAIN_DB, timeout=1.0)
                        conn.execute("PRAGMA journal_mode=WAL;")
                        c = conn.cursor()
                        c.execute("SELECT block_index, timestamp, transactions FROM blocks ORDER BY block_index ASC")
                        
                        coinbase_txs = []
                        for row in c:
                            b_idx = row[0]
                            b_ts = row[1]
                            b_txs = json.loads(row[2])
                            if b_txs:
                                cb_tx = b_txs[0]
                                if cb_tx['from_address'] == "COINBASE" and cb_tx['to_address'] == miner_addr:
                                    coinbase_txs.append((b_idx, b_ts, cb_tx))
                        conn.close()
                        
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
                if not p2p_node.peers:
                    print(f"\n{Fore.YELLOW}Žádné uzly nejsou uloženy.{Style.RESET_ALL}")
                else:
                    print(f"\n{Fore.YELLOW}--- Stav známých uzlů ---{Style.RESET_ALL}")
                    online_peers = p2p_node.get_online_peers()
                    for peer in p2p_node.peers:
                        if peer in online_peers:
                            status = f"{Fore.GREEN}[ONLINE]{Style.RESET_ALL}"
                        else:
                            status = f"{Fore.RED}[OFFLINE]{Style.RESET_ALL}"
                        peer_str = f"[{peer[0]}]:{peer[1]}" if ':' in peer[0] else f"{peer[0]}:{peer[1]}"
                        print(f"  {Fore.CYAN}{peer_str}{Style.RESET_ALL} {status}")
                        
            elif choice == "16":
                peer_ip = input("Zadejte IP adresu uzlu k přidání: ").strip()
                try:
                    peer_port = int(input("Zadejte port uzlu: ").strip())
                    new_peer = (peer_ip, peer_port)
                    print(f"{Fore.YELLOW}Pokouším se připojit k uzlu {new_peer}...{Style.RESET_ALL}")
                    if p2p_node.connect_to_peer(new_peer):
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
                                p2p_node.peer_listen_ports.pop(p2p_node.normalize_ip(peer_to_remove[0]), None)
                                peers_to_save = list(p2p_node.peers)
                            save_peers(peers_to_save)
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
                                    snapshot = dict(p2p_node.blacklist)
                                save_blacklist(snapshot)
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
                print(f"\n{Fore.YELLOW}Ukládám a vypínám...{Style.RESET_ALL}")
                save_data(droid_chain, wallets, password, p2p_node.peers, full=True, save_wallets=True)
                if os.path.exists(MEMPOOL_DB):
                    os.remove(MEMPOOL_DB)
                    print(f"{Fore.GREEN}Mempool databáze byla smazána.{Style.RESET_ALL}")
                break
                
        except KeyboardInterrupt:
            print(f"\n{Fore.YELLOW}Ukončuji program (CTRL+C)...{Style.RESET_ALL}")
            if 'p2p_node' in globals() and p2p_node:
                p2p_node.running = False
                # ETAPA 1: perzistentní spojení je potřeba explicitně zavřít,
                # jinak čtecí vlákna visí až do timeoutu.
                p2p_node.close_all_connections()
            save_data(droid_chain, wallets, password, p2p_node.peers if 'p2p_node' in globals() and p2p_node else [], full=True, save_wallets=True)
            if os.path.exists(MEMPOOL_DB):
                try:
                    os.remove(MEMPOOL_DB)
                    print(f"{Fore.GREEN}Mempool databáze byla smazána.{Style.RESET_ALL}")
                except OSError:
                    pass
            break
        except Exception as e:
            print(f"{Fore.RED}Došlo k chybě: {e}{Style.RESET_ALL}")

if __name__ == "__main__":
    main()
