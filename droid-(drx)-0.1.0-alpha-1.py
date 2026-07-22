import hashlib
import json
import time
import ecdsa
import binascii
import os
import threading
import socket
import sys
import queue
from colorama import Fore, Style, init
import struct
from cryptography.hazmat.primitives import hashes
from cryptography.hazmat.primitives.kdf.pbkdf2 import PBKDF2HMAC
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

init(autoreset=True)

# ----------------- GLOBÁLNÍ KONSTANTY -----------------
CHAIN_ID = 1
PROJECT_NAME = "Droid"
TICKER = "DRX"
DECIMALS = 8
MAX_SUPPLY = 100_000_000 * (10 ** DECIMALS)
BLOCK_REWARD = 50 * (10 ** DECIMALS)
HALVING_INTERVAL_BLOCKS = 1_000_000
BLOCK_TIME_SECONDS = 60
TX_FEE_MIN = int(0.00000001 * (10 ** DECIMALS))
TX_FEE_MAX = int(0.01 * (10 ** DECIMALS))
MIN_TX_AMOUNT = int(0.00000001 * (10 ** DECIMALS))
DIFFICULTY_ADJUSTMENT_INTERVAL = 10
TARGET_BLOCK_TIME = BLOCK_TIME_SECONDS * (DIFFICULTY_ADJUSTMENT_INTERVAL)
INITIAL_DIFFICULTY_BITS = 20
FIXED_TARGET = (1 << 256) >> INITIAL_DIFFICULTY_BITS
DYNAMIC_DIFFICULTY_ADJUSTMENT = True

BLOCKCHAIN_DB = 'blockchain.db'
WALLETS_FILE = 'wallets.json.enc'
MEMPOOL_DB = 'mempool.db'
PEERS_FILE = 'peers.json'
ADDRESS_BOOK_FILE = 'address_book.json'

P2P_HOST = '0.0.0.0'

GENESIS_ADDRESS = "DRX5eed3a1ebfcda2a258e09af660d5cc056cd3c57cbe164bd312000762bc7368ce4026"
GENESIS_ADDRESS_EXPECTED_HASH = "804e96365ba33513ad0d5065c751448eab3a285f23e97c6de6d36b7d7a7cf887"
GENESIS_TIMESTAMP = 1784541600
GENESIS_BLOCK_EXPECTED_HASH = "0000074548b5d2c3dd2d33111628e982ec714a44efae49373eac421cb48e2a4c"
GENESIS_AMOUNT = 50 * (10 ** DECIMALS)

MAX_BLOCK_SIZE_BYTES = 1 * 1024 * 1024
MAX_MEMPOOL_SIZE_BYTES = 10 * 1024 * 1024
CONFIRMATIONS_THRESHOLD = 6
NTP_SERVERS = ['pool.ntp.org', 'time.nist.gov', 'time.google.com']
LAST_BLOCKS_TO_KEEP = 100
MAX_PEERS = 20
RATE_LIMIT_REQUESTS = 10
RATE_LIMIT_WINDOW = 1
MAX_MESSAGE_SIZE = 10 * 1024 * 1024
ALLOW_EMPTY_BLOCKS = True

TX_RATE_LIMIT = 100
TX_RATE_WINDOW = 60
ALLOW_NTP_SERVERS = True
SOFTWARE_VERSION = "0.1.0-alpha.1"
PROTOCOL_VERSION = 1
BLOCK_VERSION = 1

CHECKPOINTS = {
    0: GENESIS_BLOCK_EXPECTED_HASH,
}

time_offset = 0

def get_ntp_time(server):
    TIME1970 = 2208988800
    try:
        client = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        client.settimeout(5)
        data = b'\x1b' + 47 * b'\0'
        client.sendto(data, (server, 123))
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
        client.close()
    return None

def sync_time_with_ntp():
    global time_offset
    available_servers = []
    if not ALLOW_NTP_SERVERS:
        print(f"{Fore.YELLOW}NTP synchronizace je vypnuta (ALLOW_NTP_SERVERS = False).{Style.RESET_ALL}")
        return

    for server in NTP_SERVERS:
        try:
            ntp_time = get_ntp_time(server)
            if ntp_time is not None:
                available_servers.append(server)
                print(f"{Fore.GREEN}NTP server {server} is available.{Style.RESET_ALL}")
                if time_offset == 0:
                    local_time = time.time()
                    time_offset = ntp_time - local_time
                    print(f"{Fore.GREEN}Time synchronized with {server}. Offset: {time_offset:.6f} seconds.{Style.RESET_ALL}")
        except Exception as e:
            print(f"{Fore.RED}NTP server {server} is unavailable: {e}{Style.RESET_ALL}")
            
    if not available_servers:
        print(f"{Fore.RED}No NTP servers available. Starting in read-only mode.{Style.RESET_ALL}")
        global read_only
        read_only = True

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
        checksum = hashlib.sha3_256(base_address.encode()).hexdigest()[:4]
        return base_address + checksum

    def sign_transaction(self, transaction):
        message = json.dumps(transaction.to_dict_for_signing(), sort_keys=True).encode()
        return binascii.hexlify(self.private_key.sign(message)).decode()

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

    def to_dict_for_signing(self):
        return {
            'chain_id': self.chain_id,
            'from_address': self.from_address,
            'to_address': self.to_address,
            'amount': self.amount,
            'fee': self.fee,
            'timestamp': self.timestamp,
            'nonce': self.nonce,
            'public_key': self.public_key,
            'data': self.data
        }

    def compute_hash(self):
        data = self.to_dict_for_signing()
        data_string = json.dumps(data, sort_keys=True)
        return hashlib.sha3_256(data_string.encode()).hexdigest()

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
        tx = Transaction(
            data['from_address'],
            data['to_address'],
            data['amount'],
            data['fee'],
            nonce=data.get('nonce', 0),
            public_key=data.get('public_key'),
            signature=data.get('signature'),
            timestamp=int(data['timestamp']) if data.get('timestamp') is not None else None,
            data=data.get('data'),
            chain_id=data.get('chain_id', CHAIN_ID)
        )
        tx.tx_id = data.get('tx_id') or tx.compute_hash()
        return tx

    def get_size(self):
        return len(json.dumps(self.to_dict()).encode('utf-8'))

    def is_valid_timestamp(self):
        return (get_time() - 86400) <= self.timestamp <= (get_time() + 600)

    def verify_signature(self):
        if self.from_address == "COINBASE":
            return True
        if not self.public_key or not self.signature:
            return False
        try:
            vk = ecdsa.VerifyingKey.from_string(binascii.unhexlify(self.public_key), curve=ecdsa.SECP256k1, hashfunc=hashlib.sha3_256)
            message = json.dumps(self.to_dict_for_signing(), sort_keys=True).encode()
            return vk.verify(binascii.unhexlify(self.signature), message)
        except (ecdsa.BadSignatureError, binascii.Error, ecdsa.MalformedPointError):
            return False

    def verify_sender_identity(self):
        if self.from_address == "COINBASE":
            return True
        if not self.public_key:
            return False
        try:
            public_key_bytes = binascii.unhexlify(self.public_key)
            generated_address = Wallet.public_key_to_address(public_key_bytes)
            if len(self.from_address) != 71:
                return False
            return self.from_address == generated_address
        except binascii.Error:
            return False

def compute_merkle_root(transactions):
    if not transactions:
        return hashlib.sha3_256(b'').hexdigest()
    tx_hashes = [tx.tx_id for tx in transactions]
    while len(tx_hashes) > 1:
        if len(tx_hashes) % 2 != 0:
            tx_hashes.append(tx_hashes[-1])
        new_hashes = []
        for i in range(0, len(tx_hashes), 2):
            combined = tx_hashes[i] + tx_hashes[i + 1]
            new_hash = hashlib.sha3_256(combined.encode()).hexdigest()
            new_hashes.append(new_hash)
        tx_hashes = new_hashes
    return tx_hashes[0]

class Block:
    def __init__(self, index, transactions, previous_hash, target, nonce=0, timestamp=None, version=BLOCK_VERSION, chain_id=CHAIN_ID):
        self.version = version
        self.chain_id = chain_id
        self.index = index
        self.timestamp = timestamp or get_time()
        self.transactions = transactions
        self.merkle_root = compute_merkle_root(transactions)
        self.previous_hash = previous_hash
        self.target = target
        self.nonce = nonce
        self.hash = self.compute_hash()

    def compute_hash(self):
        block_dict = {
            'version': self.version,
            'chain_id': self.chain_id,
            'index': self.index,
            'timestamp': self.timestamp,
            'merkle_root': self.merkle_root,
            'previous_hash': self.previous_hash,
            'target': hex(self.target)[2:],
            'nonce': self.nonce
        }
        block_string = json.dumps(block_dict, sort_keys=True)
        return hashlib.sha3_256(block_string.encode()).hexdigest()

    def get_size(self):
        return len(json.dumps(self.to_dict()).encode('utf-8'))

    def to_dict(self):
        return {
            'version': self.version,
            'chain_id': self.chain_id,
            'index': self.index,
            'timestamp': self.timestamp,
            'transactions': [tx.to_dict() for tx in self.transactions],
            'merkle_root': self.merkle_root,
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
            chain_id=data.get('chain_id', CHAIN_ID)
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
        self.all_tx_ids = set()
        self.balance_map = {}
        self.nonce_map = {}
        self.total_supply = 0
        
        self.orphan_pool = {}
        self.orphan_parents = defaultdict(list)
        self.cumulative_work = 0
        
        self.last_target_log_idx = -1

        if create_genesis:
            self.create_genesis_block()

    def cleanup_mempool(self):
        current_time = get_time()
        original_count = len(self.unconfirmed_transactions)
        self.unconfirmed_transactions = [
            tx for tx in self.unconfirmed_transactions
            if (current_time - tx.timestamp) <= 86400
        ]
        if len(self.unconfirmed_transactions) < original_count:
            save_mempool(self.unconfirmed_transactions)

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
            data="Darkwalker"
        )
        genesis_block = Block(0, [genesis_tx], "0", FIXED_TARGET, nonce=2555259, timestamp=GENESIS_TIMESTAMP, version=BLOCK_VERSION, chain_id=CHAIN_ID)
        
        self.chain.append(genesis_block)
        self.max_block_index = 0
        self.all_tx_ids.add(genesis_tx.tx_id)
        self.update_state_with_block(genesis_block)
        
        print(f"{Fore.GREEN}Genesis blok vytvořen a přidán do řetězce!{Style.RESET_ALL}")

    def update_state_with_block(self, block):
        for tx in block.transactions:
            self.all_tx_ids.add(tx.tx_id)
            if tx.from_address == "COINBASE":
                self.balance_map[tx.to_address] = self.balance_map.get(tx.to_address, 0) + tx.amount
            else:
                self.balance_map[tx.from_address] = self.balance_map.get(tx.from_address, 0) - tx.amount - tx.fee
                self.balance_map[tx.to_address] = self.balance_map.get(tx.to_address, 0) + tx.amount
                self.nonce_map[tx.from_address] = max(self.nonce_map.get(tx.from_address, -1), tx.nonce)
        self.cumulative_work += (1 << 256) // block.target if block.target > 0 else 0
        
        halvings = block.index // HALVING_INTERVAL_BLOCKS
        if block.index == 0:
            subsidy = GENESIS_AMOUNT
        else:
            subsidy = BLOCK_REWARD // (2 ** halvings)
        self.total_supply += subsidy

    def rebuild_state(self):
        conn = sqlite3.connect(BLOCKCHAIN_DB, timeout=1.0)
        c = conn.cursor()
        c.execute("SELECT block_index, timestamp, transactions, previous_hash, target_hex, nonce, block_hash, merkle_root, version, chain_id FROM blocks ORDER BY block_index")
        
        self.balance_map = {}
        self.nonce_map = {}
        self.all_tx_ids = set()
        self.cumulative_work = 0
        self.total_supply = 0
        
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
                'chain_id': row[9]
            }
            block = Block.from_dict(block_data)
            self.update_state_with_block(block)
            
        conn.close()

    def get_block_from_db(self, index):
        conn = sqlite3.connect(BLOCKCHAIN_DB, timeout=1.0)
        c = conn.cursor()
        c.execute("SELECT block_index, timestamp, transactions, previous_hash, target_hex, nonce, block_hash, merkle_root, version, chain_id FROM blocks WHERE block_index = ?", (index,))
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
                'chain_id': row[9]
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
        confirmed_nonce = self.nonce_map.get(address, -1)
        pending_count = sum(1 for tx in self.unconfirmed_transactions if tx.from_address == address)
        return confirmed_nonce + 1 + pending_count

    def get_pending_balance(self, wallet_address):
        balance_change = 0
        for tx in self.unconfirmed_transactions:
            if tx.from_address == wallet_address:
                balance_change -= tx.amount + tx.fee
            if tx.to_address == wallet_address:
                balance_change += tx.amount
        return balance_change

    def get_balance(self, wallet_address):
        return self.get_confirmed_balance(wallet_address) + self.get_pending_balance(wallet_address)

    def get_confirmed_balance(self, wallet_address):
        return self.balance_map.get(wallet_address, 0)

    def get_total_supply(self):
        return self.total_supply

    def get_cumulative_work(self, up_to_index=None):
        if up_to_index is None or up_to_index == self.max_block_index:
            return self.cumulative_work
            
        total_work = 0
        conn = sqlite3.connect(BLOCKCHAIN_DB, timeout=1.0)
        c = conn.cursor()
        c.execute("SELECT target_hex FROM blocks WHERE block_index <= ?", (up_to_index,))
        rows = c.fetchall()
        for row in rows:
            target = int(row[0], 16)
            work = (1 << 256) // target if target > 0 else 0
            total_work += work
        conn.close()
        return total_work

    def add_transaction(self, transaction):
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
                
            mempool_size = sum(tx.get_size() for tx in self.unconfirmed_transactions)
            if mempool_size + transaction.get_size() > MAX_MEMPOOL_SIZE_BYTES:
                print(f"{Fore.RED}Chyba:{Style.RESET_ALL} Mempool je plný, nová transakce byla odmítnuta.")
                return False

            if not transaction.is_valid_timestamp():
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

            self.unconfirmed_transactions.append(transaction)
            return True
        finally:
            self.lock.release()

    def is_tx_id_in_chain(self, tx_id):
        if tx_id in self.all_tx_ids:
            return True
            
        conn = sqlite3.connect(BLOCKCHAIN_DB, timeout=1.0)
        c = conn.cursor()
        escaped_tx_id = tx_id.replace('\\', '\\\\').replace('%', '\\%').replace('_', '\\_')
        c.execute("SELECT transactions FROM blocks WHERE transactions LIKE ? ESCAPE '\\'", (f'%"{escaped_tx_id}"%',))
        rows = c.fetchall()
        for row in rows:
            txs = json.loads(row[0])
            if any(tx.get('tx_id') == tx_id for tx in txs):
                conn.close()
                return True
        conn.close()
        return False

    def get_target(self, new_timestamp=None):
        if not DYNAMIC_DIFFICULTY_ADJUSTMENT:
            return FIXED_TARGET
            
        last_block = self.get_last_block()
        new_block_index = last_block.index + 1
        
        current_ts = new_timestamp if new_timestamp is not None else get_time()
        time_diff = current_ts - last_block.timestamp
        if time_diff > 3600:
            eda_target = last_block.target + (last_block.target // 4)
            return min(eda_target, FIXED_TARGET)
            
        if new_block_index < DIFFICULTY_ADJUSTMENT_INTERVAL:
            return FIXED_TARGET
            
        if new_block_index % DIFFICULTY_ADJUSTMENT_INTERVAL != 0:
            return last_block.target
            
        first_index = new_block_index - DIFFICULTY_ADJUSTMENT_INTERVAL
        first_block = self.get_block(first_index)
        
        if not first_block:
            return FIXED_TARGET
            
        mtp_last = self.get_median_time_past(new_block_index)
        mtp_first = self.get_median_time_past(first_index)
        time_elapsed = mtp_last - mtp_first
        if time_elapsed <= 0:
            time_elapsed = 1
            
        adjustment_factor = time_elapsed / TARGET_BLOCK_TIME
        adjustment_factor = max(0.25, min(adjustment_factor, 4.0))
        
        old_target = last_block.target
        new_target = int(old_target * adjustment_factor)
        new_target = max(1, new_target)
        new_target = min(new_target, FIXED_TARGET)
        
        if not hasattr(self, 'last_target_log_idx'):
            self.last_target_log_idx = -1
            
        if new_block_index != self.last_target_log_idx:
            p2p_node.add_log(
                f"{Fore.MAGENTA}ÚPRAVA TARGETU na bloku #{new_block_index}:{Style.RESET_ALL}\n"
                f"  Čas posledních {DIFFICULTY_ADJUSTMENT_INTERVAL} bloků: {time_elapsed:.2f}s (Cíl: {TARGET_BLOCK_TIME}s)\n"
                f"  Faktor úpravy: {adjustment_factor:.4f}\n"
                f"  Starý target (hex): {hex(old_target)[2:]} -> Nový target (hex): {hex(new_target)[2:]}"
            )
            self.last_target_log_idx = new_block_index
            
        return new_target

    def get_median_time_past(self, new_block_index, chain=None):
        MTP_SPAN = 11
        first_index = max(0, new_block_index - MTP_SPAN)

        if chain is None:
            timestamps = [b.timestamp for b in (self.get_block(i) for i in range(first_index, new_block_index)) if b is not None]
        else:
            timestamps = [chain[i].timestamp for i in range(first_index, new_block_index)]

        if not timestamps:
            return GENESIS_TIMESTAMP

        timestamps.sort()
        count = len(timestamps)
        mid = count // 2
        if count % 2 == 1:
            return timestamps[mid]
        return (timestamps[mid - 1] + timestamps[mid]) // 2

    def calculate_expected_target(self, new_block_index, chain=None, new_timestamp=None):
        if not DYNAMIC_DIFFICULTY_ADJUSTMENT:
            return FIXED_TARGET
            
        if chain is None:
            last_block = self.get_block(new_block_index - 1)
        else:
            last_block = chain[new_block_index - 1]
            
        if not last_block:
            return FIXED_TARGET
            
        if new_timestamp is not None:
            time_diff = new_timestamp - last_block.timestamp
            if time_diff > 3600:
                eda_target = last_block.target + (last_block.target // 4)
                return min(eda_target, FIXED_TARGET)
                
        if new_block_index < DIFFICULTY_ADJUSTMENT_INTERVAL:
            return FIXED_TARGET
            
        if new_block_index % DIFFICULTY_ADJUSTMENT_INTERVAL != 0:
            return last_block.target
            
        first_index = new_block_index - DIFFICULTY_ADJUSTMENT_INTERVAL
        if chain is None:
            first_block = self.get_block(first_index)
        else:
             first_block = chain[first_index]
            
        if not first_block:
            return FIXED_TARGET
            
        mtp_last = self.get_median_time_past(new_block_index, chain=chain)
        mtp_first = self.get_median_time_past(first_index, chain=chain)
        time_elapsed = mtp_last - mtp_first
        if time_elapsed <= 0:
            time_elapsed = 1
            
        adjustment_factor = time_elapsed / TARGET_BLOCK_TIME
        adjustment_factor = max(0.25, min(adjustment_factor, 4.0))
        
        old_target = last_block.target
        new_target = int(old_target * adjustment_factor)
        new_target = max(1, new_target)
        new_target = min(new_target, FIXED_TARGET)
        return new_target

    @staticmethod
    def mining_worker(block_data, start_nonce, step, result_queue, stop_event, update_interval=1.0, worker_id=0):
        index = block_data['index']
        timestamp = block_data['timestamp']
        merkle_root = block_data['merkle_root']
        previous_hash = block_data['previous_hash']
        target_hex = block_data['target']
        version = block_data.get('version', BLOCK_VERSION)
        chain_id = block_data.get('chain_id', CHAIN_ID)
        
        original_target = int(target_hex, 16)
        previous_target = block_data.get('previous_target', FIXED_TARGET)
        previous_timestamp = block_data.get('previous_timestamp', timestamp)
        target = original_target
        
        nonce = start_nonce
        hashes_calculated = 0
        last_update_time = time.time()
        
        while not stop_event.is_set():
            current_time = time.time()
            if current_time - timestamp > 60:
                timestamp = int(current_time)
                nonce = start_nonce
                
                time_diff = timestamp - previous_timestamp
                if time_diff > 3600:
                    eda_target = previous_target + (previous_target // 4)
                    target = min(eda_target, FIXED_TARGET)
                else:
                    target = original_target
                    
                if worker_id == 0:
                    formatted_time = time.strftime("%d.%m.%Y %H:%M:%S UTC+00:00", time.gmtime(timestamp))
                    sys.stdout.write(f"\n{Fore.YELLOW}Reset PoW Nonce{Style.RESET_ALL}\n")
                    sys.stdout.write(f"{Fore.CYAN}Nový timestamp:{Style.RESET_ALL} {formatted_time}\n")
                    sys.stdout.write(f"{Fore.MAGENTA}Target:{Style.RESET_ALL} {hex(target)[2:]}\n\n")
                    sys.stdout.flush()
                    
            block_dict = {
                'version': version,
                'chain_id': chain_id,
                'index': index,
                'timestamp': timestamp,
                'merkle_root': merkle_root,
                'previous_hash': previous_hash,
                'target': hex(target)[2:],
                'nonce': nonce
            }
            block_string = json.dumps(block_dict, sort_keys=True)
            computed_hash = hashlib.sha3_256(block_string.encode()).hexdigest()
            
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
                'previous_hash': block.previous_hash,
                'target': hex(block.target)[2:],
                'version': block.version,
                'chain_id': block.chain_id,
                'previous_timestamp': last_block.timestamp,
                'previous_target': last_block.target
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
            for p in processes:
                p.join()
                
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
            for p in processes:
                p.join()
            print(f"\n{Fore.YELLOW}Těžba byla ukončena uživatelem (CTRL+C).{Style.RESET_ALL}")
            return None

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
            
            if previous_hash != block.previous_hash:
                if block.index == previous_block.index:
                    prev_prev = self.get_block(block.index - 1)
                    if prev_prev and prev_prev.hash == block.previous_hash:
                        current_work = (1 << 256) // previous_block.target if previous_block.target > 0 else 0
                        new_work = (1 << 256) // block.target if block.target > 0 else 0
                        
                        if new_work > current_work or (new_work == current_work and block.hash < previous_block.hash):
                            p2p_node.add_log(f"{Fore.YELLOW}Detekován lepší konkurenční blok na stejné výšce. Provádím mini-reorg.{Style.RESET_ALL}")
                            self.chain.pop()
                            self.max_block_index -= 1
                            conn = sqlite3.connect(BLOCKCHAIN_DB, timeout=1.0)
                            c = conn.cursor()
                            c.execute("DELETE FROM blocks WHERE block_index = ?", (previous_block.index,))
                            conn.commit()
                            conn.close()
                            self.rebuild_state()
                            previous_block = prev_prev
                            previous_hash = previous_block.hash
                        else:
                            return False
                    else:
                        return False
                else:
                    return False

            if block.index != previous_block.index + 1:
                return False

            median_time_past = self.get_median_time_past(block.index)
            if not block.is_valid_timestamp(median_time_past):
                p2p_node.add_log(f"{Fore.RED}Chyba ověření bloku:{Style.RESET_ALL} Timestamp bloku je neplatný.")
                return False

            if block.target != self.get_target(new_timestamp=block.timestamp):
                return False

            if block.target != self.calculate_expected_target(block.index, new_timestamp=block.timestamp):
                p2p_node.add_log(f"{Fore.RED}Chyba ověření bloku: Nesprávný target bloku.{Style.RESET_ALL}")
                return False

            if block.merkle_root != compute_merkle_root(block.transactions):
                p2p_node.add_log(f"{Fore.RED}Chyba ověření bloku: Nesprávný Merkle root.{Style.RESET_ALL}")
                return False

            if not self.meets_difficulty(proof, block.target):
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

                if tx.chain_id != CHAIN_ID:
                    p2p_node.add_log(f"{Fore.RED}Chyba ověření bloku:{Style.RESET_ALL} Transakce patří k jinému chain_id.")
                    return False

                if self.is_tx_id_in_chain(tx.tx_id):
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
                expected_nonce = self.nonce_map.get(sender, -1) + 1
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
                    if not (TX_FEE_MIN <= tx.fee <= TX_FEE_MAX):
                        p2p_node.add_log(f"{Fore.RED}Chyba ověření bloku: Poplatek transakce mimo rozsah.{Style.RESET_ALL}")
                        return False

            coinbase_txs = [tx for tx in block.transactions if tx.from_address == "COINBASE"]
            if len(coinbase_txs) != 1:
                p2p_node.add_log(f"{Fore.RED}Chyba ověření bloku: Nesprávný počet coinbase transakcí (očekávána 1).{Style.RESET_ALL}")
                return False
            if block.transactions[0].from_address != "COINBASE":
                p2p_node.add_log(f"{Fore.RED}Chyba ověření bloku: Coinbase transakce musí být první v bloku.{Style.RESET_ALL}")
                return False

            coinbase_tx = coinbase_txs[0]
            halvings = block.index // HALVING_INTERVAL_BLOCKS
            expected_reward = BLOCK_REWARD // (2 ** halvings) if block.index > 0 else GENESIS_AMOUNT
            total_fees = sum(tx.fee for tx in block.transactions if tx.from_address != "COINBASE")
            
            if coinbase_tx.amount != expected_reward + total_fees:
                p2p_node.add_log(f"{Fore.RED}Chyba ověření bloku: Nesprávná coinbase odměna.{Style.RESET_ALL}")
                return False

            if self.get_total_supply() + coinbase_tx.amount > MAX_SUPPLY:
                p2p_node.add_log(f"{Fore.RED}Chyba ověření bloku: Překročení maximální nabídky mincí.{Style.RESET_ALL}")
                return False

            if not ALLOW_EMPTY_BLOCKS and len(block.transactions) <= 1:
                p2p_node.add_log(f"{Fore.RED}Chyba ověření bloku: Blok je prázdný (obsahuje pouze coinbase transakci).{Style.RESET_ALL}")
                return False

            temp_balance_changes = defaultdict(int)
            for tx in block.transactions:
                if tx.from_address != "COINBASE":
                    current_balance = self.balance_map.get(tx.from_address, 0) + temp_balance_changes[tx.from_address]
                    if current_balance < tx.amount + tx.fee:
                        p2p_node.add_log(f"{Fore.RED}Chyba ověření bloku: Nedostatečný zůstatek pro transakci {tx.tx_id} od {tx.from_address}.{Style.RESET_ALL}")
                        return False
                    temp_balance_changes[tx.from_address] -= (tx.amount + tx.fee)
                    temp_balance_changes[tx.to_address] += tx.amount
                else:
                    temp_balance_changes[tx.to_address] += tx.amount

            block.hash = proof
            self.chain.append(block)
            self.max_block_index = block.index
            
            if len(self.chain) > LAST_BLOCKS_TO_KEEP:
                self.chain = self.chain[-LAST_BLOCKS_TO_KEEP:]
                
            self.update_state_with_block(block)
            
            conn = sqlite3.connect(BLOCKCHAIN_DB, timeout=1.0)
            c = conn.cursor()
            transactions_json = json.dumps([tx.to_dict() for tx in block.transactions])
            target_hex = hex(block.target)[2:]
            c.execute('''
                INSERT OR REPLACE INTO blocks (block_index, timestamp, transactions, previous_hash, target_hex, nonce, block_hash, merkle_root, version, chain_id)
                VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
            ''', (block.index, block.timestamp, transactions_json, block.previous_hash, target_hex, block.nonce, block.hash, block.merkle_root, block.version, block.chain_id))
            conn.commit()
            conn.close()
            
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
            if self.add_transaction(tx):
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
        self.cleanup_mempool()
        try:
            new_block_index = self.max_block_index + 1
            halvings = new_block_index // HALVING_INTERVAL_BLOCKS
            current_reward = BLOCK_REWARD // (2 ** halvings)
            
            mining_reward = Transaction("COINBASE", miner_address, 0, nonce=0, public_key=None, signature=None, data=None, chain_id=CHAIN_ID)
            new_block_transactions = [mining_reward]
            current_block_size = 0
            
            dummy_block = Block(self.max_block_index + 1, [], self.get_last_block().hash, self.get_target(new_timestamp=mining_reward.timestamp), version=BLOCK_VERSION, chain_id=CHAIN_ID)
            current_block_size += dummy_block.get_size()
            current_block_size += mining_reward.get_size()
            
            total_fees = 0
            tx_by_sender = {}
            for tx in self.unconfirmed_transactions:
                if tx.from_address not in tx_by_sender:
                    tx_by_sender[tx.from_address] = []
                tx_by_sender[tx.from_address].append(tx)
                
            for sender in tx_by_sender:
                tx_by_sender[sender].sort(key=lambda tx: tx.nonce)
                
            pq = []
            for sender, txs in tx_by_sender.items():
                if txs:
                    first_tx = txs[0]
                    heapq.heappush(pq, (-first_tx.fee, first_tx.timestamp, first_tx.tx_id, sender))
                    
            selected_txs = []
            while pq:
                _, _, _, sender = heapq.heappop(pq)
                if sender not in tx_by_sender or not tx_by_sender[sender]:
                    continue
                tx = tx_by_sender[sender].pop(0)
                
                tx_size = tx.get_size()
                if current_block_size + tx_size > MAX_BLOCK_SIZE_BYTES:
                    tx_by_sender[sender].insert(0, tx)
                    continue
                selected_txs.append(tx)
                current_block_size += tx_size
                total_fees += tx.fee
                if tx_by_sender[sender]:
                    next_tx = tx_by_sender[sender][0]
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
                        
            new_block_transactions += selected_txs
            
            if not ALLOW_EMPTY_BLOCKS and len(new_block_transactions) == 1 and not self.unconfirmed_transactions:
                print(f"{Fore.YELLOW}Upozornění:{Style.RESET_ALL} V mempoolu nejsou žádné transakce k vytěžení. Těžba nebyla spuštěna.")
                return False
                
            final_reward = current_reward + total_fees
            if final_reward == 0:
                print(f"{Fore.YELLOW}Upozornění:{Style.RESET_ALL} Maximální nabídka byla dosažena a nejsou k dispozici žádné transakce k vytěžení.")
                return False
                
            if self.get_total_supply() + current_reward > MAX_SUPPLY:
                print(f"{Fore.RED}Chyba:{Style.RESET_ALL} Maximální nabídka dosažena, nelze vytěžit další blok.")
                return False
                
            new_block_transactions[0] = Transaction("COINBASE", miner_address, final_reward, nonce=0, public_key=None, signature=None, timestamp=mining_reward.timestamp, data=None, chain_id=CHAIN_ID)
            last_block = self.get_last_block()
            target = self.get_target(new_timestamp=mining_reward.timestamp)
            new_block = Block(
                index=last_block.index + 1,
                transactions=new_block_transactions,
                previous_hash=last_block.hash,
                target=target,
                version=BLOCK_VERSION,
                chain_id=CHAIN_ID
            )
            
            if self.get_last_block().hash != last_block.hash:
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
                
            if self.get_last_block().hash != last_block.hash:
                print(f"{Fore.YELLOW}Těžba zrušena: Mezitím přišel nový blok od jiného uzlu.{Style.RESET_ALL}")
                return False
                
            proof = self.proof_of_work(new_block, num_cores)
            if proof is None:
                return False
                
            with self.lock:
                if self.get_last_block().hash != last_block.hash:
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
                    
                    confirmed_tx_ids = {tx.tx_id for tx in new_block_transactions if tx.from_address != "COINBASE"}
                    self.unconfirmed_transactions = [
                        tx for tx in self.unconfirmed_transactions
                        if tx.tx_id not in confirmed_tx_ids
                    ]
                    
                    save_mempool(self.unconfirmed_transactions)
                    p2p_node.send_data_to_peers({'type': 'new_block', 'data': new_block.to_dict()})
                    return new_block.index
                    
            return False
        except KeyboardInterrupt:
            self.mining_in_progress = False
            print(f"\n{Fore.YELLOW}Těžba byla ukončena uživatelem (CTRL+C).{Style.RESET_ALL}")
            return False

    def is_valid_chain(self, chain=None):
        global p2p_node
        if 'p2p_node' not in globals() or p2p_node is None:
            class DummyNode:
                def add_log(self, msg):
                    print(msg)
            p2p_node = DummyNode()
            
        if chain is None:
            conn = sqlite3.connect(BLOCKCHAIN_DB, timeout=1.0)
            c = conn.cursor()
            c.execute("SELECT block_index, timestamp, transactions, previous_hash, target_hex, nonce, block_hash, merkle_root, version, chain_id FROM blocks ORDER BY block_index")
            rows = c.fetchall()
            conn.close()
            chain = [Block.from_dict({
                'index': row[0],
                'timestamp': row[1],
                'transactions': json.loads(row[2]),
                'previous_hash': row[3],
                'target': row[4],
                'nonce': row[5],
                'hash': row[6],
                'merkle_root': row[7],
                'version': row[8],
                'chain_id': row[9]
            }) for row in rows]
            
        for checkpoint_index, expected_hash in CHECKPOINTS.items():
            if checkpoint_index < len(chain):
                if chain[checkpoint_index].hash != expected_hash:
                    p2p_node.add_log(f"{Fore.RED}Chyba ověření řetězce: Blok #{checkpoint_index} neodpovídá checkpointu (očekáváno: {expected_hash}).{Style.RESET_ALL}")
                    return False
                    
        seen_tx_ids = set()
        nonce_maps = {}
        total_supply = 0
        balance_map = {}
        genesis_block = chain[0]

        if genesis_block.get_size() > MAX_BLOCK_SIZE_BYTES:
            p2p_node.add_log(f"{Fore.RED}Chyba ověření řetězce: Velikost Genesis bloku překračuje maximální povolenou velikost.{Style.RESET_ALL}")
            return False
        
        if genesis_block.hash != genesis_block.compute_hash():
            p2p_node.add_log(f"{Fore.RED}Chyba ověření řetězce: Hash genesis bloku neodpovídá jeho obsahu (podvržený genesis).{Style.RESET_ALL}")
            return False
            
        if genesis_block.index != 0 or genesis_block.previous_hash != "0" or genesis_block.target != FIXED_TARGET or genesis_block.chain_id != CHAIN_ID or genesis_block.version != BLOCK_VERSION:
            p2p_node.add_log(f"{Fore.RED}Chyba ověření řetězce: Nesprávné vlastnosti genesis bloku.{Style.RESET_ALL}")
            return False

        if genesis_block.timestamp != GENESIS_TIMESTAMP:
            p2p_node.add_log(f"{Fore.RED}Chyba ověření řetězce: Podvržený genesis blok! Čas neodpovídá oficiálnímu datu spuštění sítě.{Style.RESET_ALL}")
            return False
            
        if len(genesis_block.transactions) != 1 or genesis_block.transactions[0].from_address != "COINBASE":
            p2p_node.add_log(f"{Fore.RED}Chyba ověření řetězce: Nesprávná coinbase v genesis bloku.{Style.RESET_ALL}")
            return False
            
        genesis_tx = genesis_block.transactions[0]
        if genesis_tx.to_address != GENESIS_ADDRESS or genesis_tx.amount != GENESIS_AMOUNT or genesis_tx.timestamp != GENESIS_TIMESTAMP:
            p2p_node.add_log(f"{Fore.RED}Chyba ověření řetězce: Nesprávné konstanty v genesis transakci.{Style.RESET_ALL}")
            return False
            
        if genesis_block.merkle_root != compute_merkle_root(genesis_block.transactions):
            p2p_node.add_log(f"{Fore.RED}Chyba ověření řetězce: Nesprávný Merkle root v genesis bloku.{Style.RESET_ALL}")
            return False
            
        if genesis_tx.data != "Darkwalker":
            p2p_node.add_log(f"{Fore.RED}Chyba ověření řetězce: Nesprávná zpráva v genesis coinbase.{Style.RESET_ALL}")
            return False
            
        total_supply += GENESIS_AMOUNT
        balance_map[genesis_tx.to_address] = balance_map.get(genesis_tx.to_address, 0) + genesis_tx.amount
        
        for i in range(1, len(chain)):
            current_block = chain[i]
            previous_block = chain[i-1]
            current_block_size = current_block.get_size()
            
            if current_block_size > MAX_BLOCK_SIZE_BYTES:
                p2p_node.add_log(f"{Fore.RED}Chyba ověření řetězce: Velikost bloku #{current_block.index} ({current_block_size} bajtů) překračuje maximální povolenou velikost {MAX_BLOCK_SIZE_BYTES} bajtů.{Style.RESET_ALL}")
                return False

            if current_block.chain_id != CHAIN_ID:
                p2p_node.add_log(f"{Fore.RED}Chyba ověření řetězce: Neplatné chain_id u bloku #{current_block.index}.{Style.RESET_ALL}")
                return False
                
            if current_block.version != BLOCK_VERSION:
                p2p_node.add_log(f"{Fore.RED}Chyba ověření řetězce: Neplatná verze bloku #{current_block.index}.{Style.RESET_ALL}")
                return False
                
            if current_block.hash != current_block.compute_hash():
                return False
                
            if current_block.previous_hash != previous_block.hash:
                return False
                
            if current_block.index != previous_block.index + 1:
                p2p_node.add_log(f"{Fore.RED}Chyba ověření řetězce: Návaznost indexů přerušena u bloku #{current_block.index}.{Style.RESET_ALL}")
                return False
                
            median_time_past = self.get_median_time_past(current_block.index, chain=chain)
            if not current_block.is_valid_timestamp(median_time_past):
                p2p_node.add_log(f"{Fore.RED}Chyba ověření bloku: Timestamp bloku #{current_block.index} v řetězci je neplatný.{Style.RESET_ALL}")
                return False
                
            if current_block.target != self.calculate_expected_target(current_block.index, chain=chain, new_timestamp=current_block.timestamp):
                p2p_node.add_log(f"{Fore.RED}Chyba ověření řetězce: Nesprávný target bloku #{current_block.index}.{Style.RESET_ALL}")
                return False
                
            if current_block.merkle_root != compute_merkle_root(current_block.transactions):
                p2p_node.add_log(f"{Fore.RED}Chyba ověření řetězce: Nesprávný Merkle root v bloku #{current_block.index}.{Style.RESET_ALL}")
                return False
                
            if not self.meets_difficulty(current_block.hash, current_block.target):
                return False
                
            if any(tx.data is not None for tx in current_block.transactions):
                p2p_node.add_log(f"{Fore.RED}Chyba ověření řetězce: Nepovolená zpráva v bloku mimo genesis #{current_block.index}.{Style.RESET_ALL}")
                return False
                
            coinbase_txs = [tx for tx in current_block.transactions if tx.from_address == "COINBASE"]
            if len(coinbase_txs) != 1:
                p2p_node.add_log(f"{Fore.RED}Chyba ověření řetězce: Nesprávný počet coinbase transakcí v bloku #{current_block.index} (očekávána 1).{Style.RESET_ALL}")
                return False
                
            if current_block.transactions[0].from_address != "COINBASE":
                p2p_node.add_log(f"{Fore.RED}Chyba ověření řetězce: Coinbase transakce musí být první v bloku #{current_block.index}.{Style.RESET_ALL}")
                return False
                
            coinbase_tx = coinbase_txs[0]
            halvings = current_block.index // HALVING_INTERVAL_BLOCKS
            expected_reward = BLOCK_REWARD // (2 ** halvings)
            total_fees = sum(tx.fee for tx in current_block.transactions if tx.from_address != "COINBASE")
            
            if coinbase_tx.amount != expected_reward + total_fees:
                p2p_node.add_log(f"{Fore.RED}Chyba ověření řetězce: Nesprávná coinbase odměna v bloku #{current_block.index}.{Style.RESET_ALL}")
                return False
                
            total_supply += coinbase_tx.amount
            if total_supply > MAX_SUPPLY:
                p2p_node.add_log(f"{Fore.RED}Chyba ověření řetězce: Překročení maximální nabídky mincí po bloku #{current_block.index}.{Style.RESET_ALL}")
                return False
                
            block_tx_ids = set()
            block_nonce_map = {}
            
            for tx in current_block.transactions:
                if not isinstance(tx.amount, int) or not isinstance(tx.fee, int) or not isinstance(tx.nonce, int):
                    p2p_node.add_log(f"{Fore.RED}Chyba ověření řetězce: Hodnoty amount, fee a nonce musí být celá čísla.{Style.RESET_ALL}")
                    return False
                if tx.chain_id != CHAIN_ID:
                    p2p_node.add_log(f"{Fore.RED}Chyba ověření řetězce: Transakce má nesprávné chain_id.{Style.RESET_ALL}")
                    return False

                if tx.tx_id in seen_tx_ids:
                    p2p_node.add_log(f"{Fore.RED}Chyba ověření řetězce: Duplicitní TX ID {tx.tx_id} v řetězci.{Style.RESET_ALL}")
                    return False
                if tx.tx_id in block_tx_ids:
                    p2p_node.add_log(f"{Fore.RED}Chyba ověření bloku: Duplicitní TX ID {tx.tx_id} v bloku #{current_block.index}.{Style.RESET_ALL}")
                    return False
                    
                block_tx_ids.add(tx.tx_id)
                seen_tx_ids.add(tx.tx_id)
                
                if tx.from_address != "COINBASE":
                    if tx.amount <= 0:
                        p2p_node.add_log(f"{Fore.RED}Chyba ověření řetězce: Částka transakce musí být větší než 0.{Style.RESET_ALL}")
                        return False
                    if tx.amount < MIN_TX_AMOUNT:
                        p2p_node.add_log(f"{Fore.RED}Chyba ověření řetězce: Částka transakce je příliš malá.{Style.RESET_ALL}")
                        return False
                    if not (TX_FEE_MIN <= tx.fee <= TX_FEE_MAX):
                        p2p_node.add_log(f"{Fore.RED}Chyba ověření řetězce: Poplatek transakce mimo rozsah.{Style.RESET_ALL}")
                        return False
                    if tx.from_address in block_nonce_map:
                        if tx.nonce in block_nonce_map[tx.from_address]:
                            p2p_node.add_log(f"{Fore.RED}Chyba ověření bloku: Duplicitní nonce {tx.nonce} pro adresu {tx.from_address} v bloku #{current_block.index}.{Style.RESET_ALL}")
                            return False
                        block_nonce_map[tx.from_address].add(tx.nonce)
                    else:
                        block_nonce_map[tx.from_address] = {tx.nonce}
                        
                if not tx.verify_sender_identity() and tx.from_address != "COINBASE":
                    return False
                if not tx.verify_signature() and tx.from_address != "COINBASE":
                    return False
                    
            for sender, nonces_in_block in block_nonce_map.items():
                expected_nonce = (max(nonce_maps[sender]) if sender in nonce_maps else -1) + 1
                for tx_nonce in sorted(nonces_in_block):
                    if tx_nonce != expected_nonce:
                        p2p_node.add_log(f"{Fore.RED}Chyba ověření řetězce: Neplatná posloupnost nonce {tx_nonce} pro adresu {sender} v bloku #{current_block.index} (očekávána přesně {expected_nonce}).{Style.RESET_ALL}")
                        return False
                    expected_nonce += 1
                if sender in nonce_maps:
                    nonce_maps[sender].update(nonces_in_block)
                else:
                    nonce_maps[sender] = set(nonces_in_block)
                    
            temp_balance_changes = defaultdict(int)
            for tx in current_block.transactions:
                if tx.from_address != "COINBASE":
                    current_balance = balance_map.get(tx.from_address, 0) + temp_balance_changes[tx.from_address]
                    if current_balance < tx.amount + tx.fee:
                        p2p_node.add_log(f"{Fore.RED}Chyba ověření řetězce: Nedostatečný zůstatek pro transakci {tx.tx_id} od {tx.from_address} v bloku #{current_block.index}.{Style.RESET_ALL}")
                        return False
                    temp_balance_changes[tx.from_address] -= (tx.amount + tx.fee)
                    temp_balance_changes[tx.to_address] += tx.amount
                else:
                    temp_balance_changes[tx.to_address] += tx.amount
                    
            for addr, change in temp_balance_changes.items():
                balance_map[addr] = balance_map.get(addr, 0) + change
                
        return True

    def get_confirmations(self, block_hash):
        conn = sqlite3.connect(BLOCKCHAIN_DB, timeout=1.0)
        c = conn.cursor()
        c.execute("SELECT block_index FROM blocks WHERE block_hash = ?", (block_hash,))
        row = c.fetchone()
        conn.close()
        if row:
            block_index = row[0]
            return self.max_block_index - block_index + 1
        return 0

    def replace_chain(self, new_chain_data):
        if not self.lock.acquire(timeout=5):
            print(f"{Fore.RED}System is busy (lock timeout). Try again later.{Style.RESET_ALL}")
            return False
        try:
            new_chain = [Block.from_dict(block_data) for block_data in new_chain_data]
            current_cum_work = self.get_cumulative_work()
            new_cum_work = sum(((1 << 256) // b.target if b.target > 0 else 0) for b in new_chain)
            current_length = self.max_block_index + 1
            new_length = len(new_chain)
            
            if not self.is_valid_chain(new_chain):
                return False
                
            if new_cum_work > current_cum_work:
                pass
            elif new_cum_work == current_cum_work:
                if new_length > current_length:
                    pass
                elif new_length == current_length:
                    if new_chain[-1].hash >= self.get_last_block().hash:
                        return False
                else:
                    return False
            else:
                return False
                
            conn = sqlite3.connect(BLOCKCHAIN_DB, timeout=1.0)
            try:
                c = conn.cursor()
                fork_index = -1
                min_length = min(self.max_block_index + 1, len(new_chain))
                
                c.execute("SELECT block_index, block_hash FROM blocks WHERE block_index < ? ORDER BY block_index", (min_length,))
                local_hashes = {row[0]: row[1] for row in c.fetchall()}
                
                for i in range(min_length):
                    if local_hashes.get(i) != new_chain[i].hash:
                        break
                    fork_index = i
                    
                if fork_index >= 0:
                    reorg_depth = self.max_block_index - fork_index
                    if reorg_depth > 0:
                        p2p_node.add_log(
                            f"{Fore.MAGENTA}REORG: hloubka {reorg_depth} bloků "
                            f"(fork od bloku #{fork_index + 1}, "
                            f"opouštím bloky #{fork_index + 1}–#{self.max_block_index}).{Style.RESET_ALL}"
                        )
                        
                new_tx_ids = set()
                for block in new_chain:
                    for tx in block.transactions:
                        new_tx_ids.add(tx.tx_id)
                        
                orphaned_transactions = []
                c.execute("SELECT block_index, transactions FROM blocks WHERE block_index > ? ORDER BY block_index", (fork_index,))
                for row in c.fetchall():
                    local_block_index = row[0]
                    local_transactions = json.loads(row[1])
                    for tx_data in local_transactions:
                        tx = Transaction.from_dict(tx_data)
                        if tx.from_address == "COINBASE":
                            p2p_node.add_log(f"{Fore.YELLOW}COINBASE transakce {tx.tx_id} z osiřelého bloku #{local_block_index} zanikla (přirozené chování).{Style.RESET_ALL}")
                        elif tx.tx_id not in new_tx_ids:
                            orphaned_transactions.append(tx)
                            
                p2p_node.add_log(f"{Fore.YELLOW}Nalezen lepší řetězec. Přepisuji opuštěnou větev v databázi novými bloky...{Style.RESET_ALL}")
                
                c.execute("DELETE FROM blocks")
                for block in new_chain:
                    transactions_json = json.dumps([tx.to_dict() for tx in block.transactions])
                    target_hex = hex(block.target)[2:]
                    c.execute("INSERT INTO blocks (block_index, timestamp, transactions, previous_hash, target_hex, nonce, block_hash, merkle_root, version, chain_id) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?)",
                              (block.index, block.timestamp, transactions_json, block.previous_hash, target_hex, block.nonce, block.hash, block.merkle_root, block.version, block.chain_id))
                conn.commit()
            finally:
                conn.close()
            
            self.rebuild_state()
            self.max_block_index = new_chain[-1].index
            self.chain = new_chain[-LAST_BLOCKS_TO_KEEP:] if len(new_chain) > LAST_BLOCKS_TO_KEEP else new_chain
            self.unconfirmed_transactions = []
            
            orphaned_transactions.sort(key=lambda x: (x.from_address, x.nonce))
            
            for tx in orphaned_transactions:
                if self.add_transaction(tx):
                    p2p_node.add_log(f"{Fore.GREEN}Osiřelá uživatelská transakce {tx.tx_id} přidána zpět do mempoolu.{Style.RESET_ALL}")
                else:
                    reason = "Neznámý důvod"
                    if self.is_tx_id_in_chain(tx.tx_id):
                        reason = "Již existuje v novém řetězci"
                    elif any(t.tx_id == tx.tx_id for t in self.unconfirmed_transactions):
                        reason = "Již existuje v mempoolu"
                    elif tx.nonce != self.get_next_nonce(tx.from_address):
                        reason = f"Navazující chyba nonce (Máte {tx.nonce}, ale síť čeká na {self.get_next_nonce(tx.from_address)}. Pravděpodobně selhala předchozí transakce.)"
                    elif self.get_confirmed_balance(tx.from_address) - sum(t.amount + t.fee for t in self.unconfirmed_transactions if t.from_address == tx.from_address) < tx.amount + tx.fee:
                        reason = "Nedostatečný zůstatek (pokus o utracení zrušené coinbase odměny nebo již utracených prostředků)"
                    else:
                        reason = "Jiná chyba ověření (např. čas, podpis)"
                    p2p_node.add_log(f"{Fore.RED}Osiřelá uživatelská transakce {tx.tx_id} zamítnuta z mempoolu. Důvod: {reason}.{Style.RESET_ALL}")
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
        c = conn.cursor()
        c.execute("SELECT block_index, transactions FROM blocks")
        for row in c:
            transactions = json.loads(row[1])
            for tx_data in transactions:
                if tx_data['tx_id'] == tx_id:
                    conn.close()
                    return Transaction.from_dict(tx_data), f"Blok #{row[0]}"
        conn.close()
        return None, None

def format_confirmations(count):
    if count == 0:
        return f"{Fore.RED}{count}{Style.RESET_ALL}"
    elif 1 <= count <= 5:
        return f"{Fore.YELLOW}{count}{Style.RESET_ALL}"
    else:
        return f"{Fore.GREEN}{count}{Style.RESET_ALL}"

def load_address_book():
    if os.path.exists(ADDRESS_BOOK_FILE):
        try:
            with open(ADDRESS_BOOK_FILE, 'r') as f:
                return json.load(f)
        except Exception:
            pass
    return {}

def save_address_book(address_book):
    try:
        with open(ADDRESS_BOOK_FILE, 'w') as f:
            json.dump(address_book, f, indent=4)
    except Exception as e:
        print(f"{Fore.RED}Chyba při ukládání adresáře: {e}{Style.RESET_ALL}")

def save_data(droid_chain, wallets, password, peers):
    try:
        conn = sqlite3.connect(BLOCKCHAIN_DB, timeout=1.0)
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
                chain_id INTEGER
            )
        ''')
        for block in droid_chain.chain:
            transactions_json = json.dumps([tx.to_dict() for tx in block.transactions])
            target_hex = hex(block.target)[2:]
            c.execute('''
                INSERT OR REPLACE INTO blocks (block_index, timestamp, transactions, previous_hash, target_hex, nonce, block_hash, merkle_root, version, chain_id)
                VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
            ''', (block.index, block.timestamp, transactions_json, block.previous_hash, target_hex, block.nonce, block.hash, block.merkle_root, block.version, block.chain_id))
        conn.commit()
        conn.close()
        
        save_wallets_enc(wallets, password)
        save_mempool(droid_chain.unconfirmed_transactions)
        save_peers(peers)
        print(f"{Fore.GREEN}Data byla úspěšně uložena.{Style.RESET_ALL}")
    except Exception as e:
        print(f"{Fore.RED}Chyba při ukládání dat:{Style.RESET_ALL} {e}")

def save_wallets_enc(wallets, password):
    wallet_data = {
        address: binascii.hexlify(wallet.private_key.to_string()).decode()
        for address, wallet in wallets.items()
    }
    data_json = json.dumps(wallet_data).encode()
    salt = os.urandom(16)
    kdf = PBKDF2HMAC(
        algorithm=hashes.SHA256(),
        length=32,
        salt=salt,
        iterations=200000,
        backend=default_backend()
    )
    key = kdf.derive(password.encode())
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
                chain_id INTEGER
            )
        ''')
        c.execute('DELETE FROM transactions')
        for tx in unconfirmed_transactions:
            c.execute('''
                INSERT INTO transactions (tx_id, from_address, to_address, amount, fee, nonce, timestamp, public_key, signature, chain_id)
                VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
            ''', (tx.tx_id, tx.from_address, tx.to_address, tx.amount, tx.fee, tx.nonce, tx.timestamp, tx.public_key, tx.signature, tx.chain_id))
        conn.commit()
        conn.close()
    except Exception as e:
        print(f"{Fore.RED}Chyba při ukládání mempoolu:{Style.RESET_ALL} {e}")

def save_peers(peers):
    try:
        with open(PEERS_FILE, 'w') as f:
            json.dump(peers, f, indent=4)
    except Exception as e:
        print(f"{Fore.RED}Chyba při ukládání peers:{Style.RESET_ALL} {e}")

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
            kdf = PBKDF2HMAC(
                algorithm=hashes.SHA256(),
                length=32,
                salt=salt,
                iterations=200000,
                backend=default_backend()
            )
            key = kdf.derive(password.encode())
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

    droid_chain = Blockchain(create_genesis=False)
    if os.path.exists(BLOCKCHAIN_DB):
        try:
            conn = sqlite3.connect(BLOCKCHAIN_DB, timeout=1.0)
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
                    chain_id INTEGER
                )
             ''')
            c.execute("SELECT MAX(block_index) FROM blocks")
            droid_chain.max_block_index = c.fetchone()[0] or 0
            
            c.execute("SELECT block_index, timestamp, transactions, previous_hash, target_hex, nonce, block_hash, merkle_root, version, chain_id FROM blocks WHERE block_index > ? ORDER BY block_index", (droid_chain.max_block_index - LAST_BLOCKS_TO_KEEP,))
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
                'chain_id': row[9]
            }) for row in rows]
            
            droid_chain.rebuild_state()
            conn.close()
            print(f"{Fore.GREEN}Blockchain byl načten z databáze.{Style.RESET_ALL}")
        except Exception as e:
            print(f"{Fore.RED}Chyba při načítání blockchainu:{Style.RESET_ALL} {e}")
            print(f"{Fore.YELLOW}Vytvářím nový blockchain s genesis blokem.{Style.RESET_ALL}")
            droid_chain.create_genesis_block()
            save_data(droid_chain, wallets, password, peers)
    else:
        print(f"{Fore.YELLOW}Databáze blockchainu nenalezena. Vytvářím nový blockchain s genesis blokem.{Style.RESET_ALL}")
        droid_chain.create_genesis_block()
        save_data(droid_chain, wallets, password, peers)
        
    print(f"{Fore.YELLOW}Provádím plnou validaci blockchain.db při startu...{Style.RESET_ALL}")
    if not droid_chain.is_valid_chain():
        print(f"{Fore.RED}CHYBA: Blockchain v blockchain.db je neplatný nebo byl ručně podvržen!{Style.RESET_ALL}")
        print(f"{Fore.RED}Program se ukončuje pro ochranu integrity sítě.{Style.RESET_ALL}")
        sys.exit(1)
        
    print(f"{Fore.GREEN}Blockchain validován úspěšně.{Style.RESET_ALL}")
    droid_chain.unconfirmed_transactions = load_mempool(droid_chain)
    
    if os.path.exists(PEERS_FILE):
        try:
            with open(PEERS_FILE, 'r') as f:
                peers_data = json.load(f)
                peers = [tuple(p) for p in peers_data]
                print(f"{Fore.GREEN}Peers byly načteny ze souboru.{Style.RESET_ALL}")
        except Exception as e:
            print(f"{Fore.RED}Chyba při načítání peers:{Style.RESET_ALL} {e}")
            
    return droid_chain, wallets, peers, password

def load_mempool(droid_chain):
    if os.path.exists(MEMPOOL_DB):
        try:
            conn = sqlite3.connect(MEMPOOL_DB, timeout=1.0)
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
                    chain_id INTEGER
                )
            ''')
            c.execute("SELECT tx_id, from_address, to_address, amount, fee, nonce, timestamp, public_key, signature, chain_id FROM transactions")
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
                    'chain_id': row[9]
                }
                tx = Transaction.from_dict(tx_data)
                if not droid_chain.add_transaction(tx):
                    print(f"{Fore.RED}Transakce z mempoolu DB zamítnuta (duplicitní nebo neplatná): {tx.tx_id}{Style.RESET_ALL}")
        except Exception as e:
            print(f"{Fore.RED}Chyba při načítání mempoolu:{Style.RESET_ALL} {e}")
            
    return droid_chain.unconfirmed_transactions

class P2PNode:
    def __init__(self, blockchain, host, port, initial_peers):
        self.blockchain = blockchain
        self.host = host
        self.port = port
        self.peers = initial_peers
        self.server_thread = threading.Thread(target=self.start_server)
        self.running = True
        self.sync_thread = threading.Thread(target=self.sync_chain_periodically)
        self.sync_thread.daemon = True
        self.p2p_log = queue.Queue()
        self.rate_limit = defaultdict(list)
        self.blacklist = set()
        self.tx_rate_limit = defaultdict(list)
        self.awaiting_full_chain = False

    def get_locator_hashes(self):
        locator = []
        try:
            conn = sqlite3.connect(BLOCKCHAIN_DB, timeout=1.0)
            c = conn.cursor()
            c.execute("SELECT block_hash FROM blocks ORDER BY block_index DESC LIMIT 50")
            for row in c.fetchall():
                locator.append(row[0])
            conn.close()
        except Exception:
            pass
        return locator

    def add_log(self, message):
        self.p2p_log.put(message)

    def is_rate_limited(self, addr):
        now = time.time()
        
        if len(self.rate_limit) > 1000:
            self.rate_limit = defaultdict(list, {k: v for k, v in self.rate_limit.items() if v and now - v[-1] < RATE_LIMIT_WINDOW})
            
        self.rate_limit[addr[0]] = [t for t in self.rate_limit[addr[0]] if now - t < RATE_LIMIT_WINDOW]
        
        if len(self.rate_limit[addr[0]]) >= RATE_LIMIT_REQUESTS:
            self.blacklist.add(addr[0])
            return True
            
        self.rate_limit[addr[0]].append(now)
        return False

    def is_blacklisted(self, addr):
        return addr[0] in self.blacklist

    def is_peer_valid(self, peer_addr):
        if len(self.peers) >= MAX_PEERS:
            return False
        return True

    def start_server(self):
        server_socket = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        server_socket.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
        try:
            server_socket.bind((self.host, self.port))
        except OSError:
            print(f"\n{Fore.RED}Chyba: Port {self.port} je již obsazen jiným procesem. Vypínám uzel.{Style.RESET_ALL}")
            self.running = False
            return
            
        server_socket.listen()
        self.add_log(f"{Fore.CYAN}Poslouchám na {self.host}:{self.port}...{Style.RESET_ALL}")
        server_socket.settimeout(1)
        
        while self.running:
            try:
                conn, addr = server_socket.accept()
                if self.is_blacklisted(addr):
                    conn.close()
                    continue
                if self.is_rate_limited(addr):
                    conn.close()
                    continue
                    
                client_thread = threading.Thread(target=self.handle_client_connection, args=(conn, addr))
                client_thread.daemon = True
                client_thread.start()
            except socket.timeout:
                pass
            except Exception as e:
                self.add_log(f"{Fore.RED}Chyba serveru: {e}{Style.RESET_ALL}")

    def handle_client_connection(self, conn, addr):
        with conn:
             conn.settimeout(10)
             try:
                 raw_msglen = conn.recv(4)
                 if not raw_msglen:
                     return
                     
                 msglen = struct.unpack('!I', raw_msglen)[0]
                 if msglen > MAX_MESSAGE_SIZE:
                     self.add_log(f"{Fore.RED}Přijatá zpráva příliš velká od {addr}: {msglen} bajtů. Odmítnuto.{Style.RESET_ALL}")
                     self.blacklist.add(addr[0])
                     return
                     
                 data_buffer = b''
                 while len(data_buffer) < msglen:
                     part = conn.recv(msglen - len(data_buffer))
                     if not part:
                         data_buffer = None
                         break
                     data_buffer += part
                     
                 if not data_buffer:
                     self.add_log(f"{Fore.RED}Spojení s {addr} přerušeno při přijímání dat.{Style.RESET_ALL}")
                     return
                     
                 if len(data_buffer) == msglen:
                     depth = 0
                     max_depth_exceeded = False
                     for byte in data_buffer:
                         if byte == 123 or byte == 91: 
                             depth += 1
                             if depth > 20:
                                max_depth_exceeded = True
                                break
                         elif byte == 125 or byte == 93:
                             depth -= 1
                             
                     if max_depth_exceeded:
                         self.add_log(f"{Fore.RED}Přijatá zpráva má příliš hluboké vnoření. Odmítnuto.{Style.RESET_ALL}")
                         self.blacklist.add(addr[0])
                         return
                         
                     message = json.loads(data_buffer.decode('utf-8'))
                     self.handle_message(message, addr)
                 else:
                     self.add_log(f"{Fore.RED}Přijata neúplná zpráva od {addr}. Očekáváno {msglen}, přijato {len(data_buffer)}.{Style.RESET_ALL}")
             except socket.timeout:
                 pass
             except json.JSONDecodeError as e:
                 self.add_log(f"{Fore.RED}Chyba dekódování JSON od {addr}: {e}{Style.RESET_ALL}")
             except Exception as e:
                 self.add_log(f"{Fore.RED}Chyba spojení s {addr}: {e}{Style.RESET_ALL}")

    def handle_message(self, message, addr=None):
        try:
            timestamp = get_time()
            formatted_time = time.strftime('%d.%m.%Y %H:%M:%S UTC+00:00', time.gmtime(timestamp))
        except Exception:
            formatted_time = "Neznámý čas"
            
        if addr:
            ip_port = f"{addr[0]}:{addr[1]}"
        else:
            ip_port = "neznámý uzel"
            
        msg_type = message.get('type')
        if not msg_type:
            self.add_log(f"{Fore.RED}Přijata zpráva bez udání typu od uzlu {ip_port}. Odmítnuto.{Style.RESET_ALL}")
            return
        
        self.add_log(f"\n{Fore.CYAN}Přijata zpráva typu: {msg_type} od uzlu {ip_port} Čas {formatted_time}{Style.RESET_ALL}")
        
        if msg_type == 'transaction':
            now = time.time()
            if len(self.tx_rate_limit) > 1000:
                self.tx_rate_limit = defaultdict(list, {k: v for k, v in self.tx_rate_limit.items() if v and now - v[-1] < TX_RATE_WINDOW})
                
            self.tx_rate_limit[addr[0]] = [t for t in self.tx_rate_limit[addr[0]] if now - t < TX_RATE_WINDOW]
            if len(self.tx_rate_limit[addr[0]]) >= TX_RATE_LIMIT:
                self.blacklist.add(addr[0])
                self.add_log(f"{Fore.RED}Překročen limit transakcí od {addr}. Uzel blacklistován.{Style.RESET_ALL}")
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
            self.add_log(f"{Fore.YELLOW}Přijat požadavek na info o řetězci, odesílám...{Style.RESET_ALL}")
            local_length = self.blockchain.max_block_index + 1
            local_last_hash = self.blockchain.get_last_block().hash
            local_cum_work = self.blockchain.get_cumulative_work()
            self.send_data_to_peers({'type': 'response_chain_info', 'data': {'length': local_length, 'last_hash': local_last_hash, 'cum_work': local_cum_work}})
            
        elif msg_type == 'response_chain_info':
            data = message['data']
            remote_length = data.get('length', 0)
            remote_last_hash = data.get('last_hash', "")
            remote_cum_work = data.get('cum_work', 0)

            local_length = self.blockchain.max_block_index + 1
            local_last_hash = self.blockchain.get_last_block().hash
            local_cum_work = self.blockchain.get_cumulative_work()

            if remote_cum_work > local_cum_work:
                self.add_log(f"{Fore.YELLOW}Detekován řetězec s větší prací. Žádám o bloky přes inkrementální sync...{Style.RESET_ALL}")
                self.send_data_to_peers({'type': 'request_blocks', 'data': {'locator_hashes': self.get_locator_hashes()}})
            elif remote_cum_work == local_cum_work:
                if remote_length > local_length:
                    self.add_log(f"{Fore.YELLOW}Stejná práce, ale delší řetězec. Žádám o bloky přes inkrementální sync...{Style.RESET_ALL}")
                    self.send_data_to_peers({'type': 'request_blocks', 'data': {'locator_hashes': self.get_locator_hashes()}})
                elif remote_length == local_length:
                    if remote_last_hash < local_last_hash:
                        self.add_log(f"{Fore.YELLOW}Stejná práce i délka, ale lepší hash (tie-breaker). Žádám o bloky přes inkrementální sync...{Style.RESET_ALL}")
                        self.send_data_to_peers({'type': 'request_blocks', 'data': {'locator_hashes': self.get_locator_hashes()}})
                    else:
                        self.add_log(f"{Fore.GREEN}Řetězce synchronizovány (stejná práce i délka, náš hash je lepší nebo stejný).{Style.RESET_ALL}")
                else:
                    self.add_log(f"{Fore.GREEN}Náš řetězec má stejnou práci, ale je delší (nebo jsme synchronizováni).{Style.RESET_ALL}")
            else:
                self.add_log(f"{Fore.GREEN}Náš řetězec má větší práci. Ignoruji vzdálený.{Style.RESET_ALL}")

        elif msg_type == 'request_blocks':
            locator_hashes = message['data'].get('locator_hashes', [])
            start_index = message['data'].get('start_index', 0)

            conn = sqlite3.connect(BLOCKCHAIN_DB, timeout=1.0)
            c = conn.cursor()

            if locator_hashes:
                for h in locator_hashes:
                    c.execute("SELECT block_index FROM blocks WHERE block_hash = ?", (h,))
                    row = c.fetchone()
                    if row:
                        start_index = row[0] + 1
                        break

            self.add_log(f"{Fore.YELLOW}Přijat požadavek na bloky, odesílám od indexu {start_index}...{Style.RESET_ALL}")
            c.execute("SELECT block_index, timestamp, transactions, previous_hash, target_hex, nonce, block_hash, merkle_root, version, chain_id FROM blocks WHERE block_index >= ? ORDER BY block_index", (start_index,))
            rows = c.fetchall()
            conn.close()

            blocks_data = []
            for row in rows:
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
                    'chain_id': row[9]
                })
            self.send_data_to_peers({'type': 'response_blocks', 'data': blocks_data})

        elif msg_type == 'response_blocks':
            blocks_data = message['data']
            if not blocks_data:
                return

            self.add_log(f"{Fore.YELLOW}Přijaty bloky ({len(blocks_data)}), zpracovávám...{Style.RESET_ALL}")
            current_index = self.blockchain.max_block_index + 1
            last_hash = self.blockchain.get_last_block().hash

            first_block_data = blocks_data[0]
            first_block_index = first_block_data['index']

            if first_block_index == current_index and first_block_data['previous_hash'] == last_hash:
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

            else:
                self.add_log(f"{Fore.YELLOW}Detekován fork (blok navazuje na starší index). Pokouším se o lokální reorg...{Style.RESET_ALL}")

                conn = sqlite3.connect(BLOCKCHAIN_DB, timeout=1.0)
                c = conn.cursor()
                c.execute("SELECT block_index, timestamp, transactions, previous_hash, target_hex, nonce, block_hash, merkle_root, version, chain_id FROM blocks WHERE block_index < ? ORDER BY block_index", (first_block_index,))
                prefix_rows = c.fetchall()
                conn.close()

                if not prefix_rows and first_block_index != 0:
                    self.add_log(f"{Fore.RED}Nedokážu navázat přijaté bloky na svůj chain. Fallback na full sync...{Style.RESET_ALL}")
                    self.awaiting_full_chain = True
                    self.send_data_to_peers({'type': 'request_full_chain'})
                    return

                full_new_chain_data = []
                for row in prefix_rows:
                    full_new_chain_data.append({
                        'index': row[0],
                        'timestamp': row[1],
                        'transactions': json.loads(row[2]),
                        'previous_hash': row[3],
                        'target': row[4],
                        'nonce': row[5],
                        'hash': row[6],
                        'merkle_root': row[7],
                        'version': row[8],
                        'chain_id': row[9]
                    })
                full_new_chain_data.extend(blocks_data)

                if self.blockchain.replace_chain(full_new_chain_data):
                    save_data(self.blockchain, wallets, password, self.peers)
                    self.add_log(f"{Fore.GREEN}Úspěšný mini-reorg pomocí inkrementální synchronizace!{Style.RESET_ALL}")
                else:
                    self.add_log(f"{Fore.RED}Navrhovaný fork není platný nebo nemá větší váhu. Odmítnuto.{Style.RESET_ALL}")
                
        elif msg_type == 'request_full_chain':
            self.add_log(f"{Fore.YELLOW}Přijat požadavek na celý řetězec, odesílám...{Style.RESET_ALL}")
            conn = sqlite3.connect(BLOCKCHAIN_DB, timeout=1.0)
            c = conn.cursor()
            c.execute("SELECT block_index, timestamp, transactions, previous_hash, target_hex, nonce, block_hash, merkle_root, version, chain_id FROM blocks ORDER BY block_index")
            rows = c.fetchall()
            chain_data = [Block.from_dict({
                'index': row[0],
                'timestamp': row[1],
                'transactions': json.loads(row[2]),
                'previous_hash': row[3],
                'target': row[4],
                'nonce': row[5],
                'hash': row[6],
                'merkle_root': row[7],
                'version': row[8],
                'chain_id': row[9]
            }).to_dict() for row in rows]
            conn.close()
            self.send_data_to_peers({'type': 'response_full_chain', 'data': chain_data})
            
        elif msg_type == 'response_full_chain':
            if not getattr(self, 'awaiting_full_chain', False):
                self.add_log(f"{Fore.YELLOW}Přijat nevyžádaný response_full_chain od uzlu {ip_port}, ignoruji.{Style.RESET_ALL}")
                return
            self.awaiting_full_chain = False
            
            new_chain_data = message.get('data', [])
            if self.blockchain.replace_chain(new_chain_data):
                save_data(self.blockchain, wallets, password, self.peers)
                self.add_log(f"{Fore.GREEN}Řetězec byl úspěšně synchronizován a uložen.{Style.RESET_ALL}")
            else:
                self.add_log(f"{Fore.YELLOW}Přijatý řetězec není lepší nebo platný, odmítám ho.{Style.RESET_ALL}")
                
        elif msg_type == 'new_block':
            new_block_data = message['data']
            new_block = Block.from_dict(new_block_data)
            
            if self.blockchain.mining_in_progress:
                self.blockchain.mining_in_progress = False
                self.add_log(f"{Fore.YELLOW}Těžba zastavena, přijat nový blok.{Style.RESET_ALL}")
                
            if self.blockchain.add_block(new_block, new_block.hash):
                self.add_log(f"{Fore.GREEN}Přijat a přidán nový blok {new_block.index} od jiného uzlu.{Style.RESET_ALL}")
                confirmed_tx_ids = {tx.tx_id for tx in new_block.transactions if tx.from_address != "COINBASE"}
                self.blockchain.unconfirmed_transactions = [
                    tx for tx in self.blockchain.unconfirmed_transactions
                    if tx.tx_id not in confirmed_tx_ids
                ]
                self.add_log(f"{Fore.YELLOW}Mempool byl aktualizován, odstraněno {len(confirmed_tx_ids)} potvrzených transakcí.{Style.RESET_ALL}")
                save_data(self.blockchain, wallets, password, self.peers)
            else:
                conn = sqlite3.connect(BLOCKCHAIN_DB, timeout=1.0)
                c = conn.cursor()
                c.execute("SELECT 1 FROM blocks WHERE block_hash = ?", (new_block.previous_hash,))
                exists = c.fetchone() is not None
                conn.close()
                if exists:
                    self.add_log(f"{Fore.YELLOW}Přijatý blok není navázaný na náš poslední blok. Zahajuji synchronizaci...{Style.RESET_ALL}")
                    self.send_data_to_peers({'type': 'request_chain_info'})
                else:
                    self.blockchain.add_orphan_block(new_block)
                    self.add_log(f"{Fore.YELLOW}Přijat orphan blok {new_block.index}, uložen do poolu.{Style.RESET_ALL}")
                
        elif msg_type == 'request_mempool':
            self.add_log(f"{Fore.YELLOW}Přijat požadavek na mempool, odesílám...{Style.RESET_ALL}")
            self.send_data_to_peers({'type': 'response_mempool', 'data': [tx.to_dict() for tx in self.blockchain.unconfirmed_transactions]})
            
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
                
            if is_allowed_ip and new_peer_addr not in self.peers and new_peer_addr != (self.host, self.port) and self.is_peer_valid(new_peer_addr):
                self.connect_to_peer(new_peer_addr)
            elif not is_allowed_ip:
                 self.add_log(f"{Fore.YELLOW}Zpráva 'new_peer' ignorována: Adresa {new_peer_addr[0]} není povolená veřejná IP.{Style.RESET_ALL}")
                
        elif msg_type == 'handshake':
            remote_protocol_version = message.get('protocol_version')
            remote_software_version = message.get('software_version', 'neznámá')
            remote_chain_id = message.get('chain_id')
            
            if remote_chain_id != CHAIN_ID:
                if addr:
                    self.blacklist.add(addr[0])
                self.add_log(f"{Fore.RED}Handshake selhal od uzlu {ip_port}: nesprávné chain_id {remote_chain_id} (očekáváno {CHAIN_ID}). Uzel blacklistován.{Style.RESET_ALL}")
            elif remote_protocol_version != PROTOCOL_VERSION:
                if addr:
                    self.blacklist.add(addr[0])
                self.add_log(f"{Fore.RED}Handshake selhal od uzlu {ip_port}: nekompatibilní protocol_version {remote_protocol_version} (očekáváno {PROTOCOL_VERSION}). Uzel blacklistován.{Style.RESET_ALL}")
            else:
                self.add_log(f"{Fore.GREEN}Handshake úspěšný od uzlu {ip_port}: software_version={remote_software_version}, protocol_version={remote_protocol_version}, chain_id={remote_chain_id}.{Style.RESET_ALL}")
                
    def connect_to_peer(self, peer_addr):
        if peer_addr not in self.peers:
            try:
                client_socket = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
                client_socket.settimeout(3)
                client_socket.connect(peer_addr)
                self.peers.append(peer_addr)
                self.add_log(f"{Fore.GREEN}Úspěšně připojeno k uzlu {peer_addr}{Style.RESET_ALL}")
                
                self.send_data_to_peers({'type': 'handshake', 'protocol_version': PROTOCOL_VERSION, 'software_version': SOFTWARE_VERSION, 'chain_id': CHAIN_ID})
                self.send_data_to_peers({'type': 'request_mempool'})
                self.send_data_to_peers({'type': 'request_chain_info'})
                
                save_peers(self.peers)
                client_socket.close()
                return True
            except ConnectionRefusedError:
                print(f"{Fore.RED}Chyba:{Style.RESET_ALL} Nelze se připojit k uzlu {peer_addr}")
            except Exception as e:
                print(f"{Fore.RED}Chyba při připojování:{Style.RESET_ALL} {e}")
        return False

    def connect_to_all_peers(self):
        for peer in list(self.peers):
            self.connect_to_peer(peer)

    def _send_to_single_peer(self, peer, data):
        try:
            client_socket = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
            client_socket.settimeout(5)
            client_socket.connect(peer)
            message = json.dumps(data).encode('utf-8')
            message_length = struct.pack('!I', len(message))
            client_socket.sendall(message_length + message)
            client_socket.close()
        except Exception as e:
            self.add_log(f"{Fore.RED}Chyba při odesílání dat uzlu {peer}: {e}{Style.RESET_ALL}")

    def send_data_to_peers(self, data):
        for peer in self.peers:
            thread = threading.Thread(target=self._send_to_single_peer, args=(peer, data))
            thread.daemon = True
            thread.start()

    def sync_chain_periodically(self):
        while self.running:
            time.sleep(10)
            self.blockchain.cleanup_mempool()
            if self.peers:
                self.add_log(f"{Fore.YELLOW}Synchronizuji blockchain a mempool se sousedními uzly...{Style.RESET_ALL}")
                self.send_data_to_peers({'type': 'request_chain_info'})
                self.send_data_to_peers({'type': 'request_mempool'})

    def check_peer_connectivity(self, peer, online_peers_list, lock):
        try:
            client_socket = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
            client_socket.settimeout(2)
            client_socket.connect(peer)
            client_socket.close()
            with lock:
                online_peers_list.append(peer)
        except (socket.timeout, ConnectionRefusedError, OSError):
            pass

    def get_online_peers(self):
        online_peers = []
        threads = []
        lock = threading.Lock()
        
        for peer in self.peers:
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
    if len(address) != 71:
        return False
        
    base = address[:-4]
    expected_checksum = hashlib.sha3_256(base.encode()).hexdigest()[:4]
    return address[-4:] == expected_checksum and all(c in '0123456789abcdef' for c in address[3:])

def show_p2p_log():
    print(f"\n{Fore.YELLOW}--- Log P2P sítě (stiskněte Enter pro návrat) ---{Style.RESET_ALL}")
    while not p2p_node.p2p_log.empty():
        print(p2p_node.p2p_log.get())
    input()

def get_mempool_size_bytes(unconfirmed_transactions):
    return sum(tx.get_size() for tx in unconfirmed_transactions)

def print_menu():
    print(f"\n{Fore.YELLOW}--- Menu ---{Style.RESET_ALL}")
    print(f"{Fore.GREEN}1{Style.RESET_ALL} - Vytěžit nový blok")
    print(f"{Fore.GREEN}2{Style.RESET_ALL} - Vytvořit transakci")
    print(f"{Fore.GREEN}3{Style.RESET_ALL} - Zobrazit nepotvrzené transakce")
    print(f"{Fore.GREEN}4{Style.RESET_ALL} - Zobrazit blockchain")
    print(f"{Fore.GREEN}5{Style.RESET_ALL} - Vytvořit novou peněženku")
    print(f"{Fore.GREEN}6{Style.RESET_ALL} - Zobrazit peněženky a zůstatky")
    print(f"{Fore.GREEN}7{Style.RESET_ALL} - Smazat peněženku")
    print(f"{Fore.GREEN}8{Style.RESET_ALL} - Importovat privátní klíč")
    print(f"{Fore.GREEN}9{Style.RESET_ALL} - Exportovat privátní klíč")
    print(f"{Fore.GREEN}10{Style.RESET_ALL} - Uložené adresy")
    print(f"{Fore.GREEN}11{Style.RESET_ALL} - Zobrazit stav uzlů")
    print(f"{Fore.GREEN}12{Style.RESET_ALL} - Ukončit a uložit")
    print(f"{Fore.GREEN}13{Style.RESET_ALL} - Zobrazit historii transakcí pro adresu")
    print(f"{Fore.GREEN}14{Style.RESET_ALL} - Zobrazit log P2P sítě")
    print(f"{Fore.GREEN}15{Style.RESET_ALL} - Zobrazit detaily transakce podle TX ID")
    print(f"{Fore.GREEN}16{Style.RESET_ALL} - Zobrazit celkovou nabídku mincí")
    print(f"{Fore.GREEN}17{Style.RESET_ALL} - Vyhledat blok podle hashe")
    print(f"{Fore.GREEN}18{Style.RESET_ALL} - Manuálně přidat nový uzel")
    print(f"{Fore.GREEN}19{Style.RESET_ALL} - Smazat uzel")
    print(f"{Fore.GREEN}20{Style.RESET_ALL} - Zobrazit blok")

def verify_genesis_address():
    current_hash = hashlib.sha3_256(GENESIS_ADDRESS.encode()).hexdigest()
    if current_hash != GENESIS_ADDRESS_EXPECTED_HASH:
        print(f"{Fore.RED}Chyba: Genesis adresa byla změněna! Program se ukončuje.{Style.RESET_ALL}")
        sys.exit(1)

def verify_genesis_block(chain):
    genesis_block = chain.get_block_from_db(0)
    if genesis_block.timestamp != GENESIS_TIMESTAMP or genesis_block.hash != GENESIS_BLOCK_EXPECTED_HASH:
        print(f"{Fore.RED}Chyba: Genesis blok byl změněn (timestamp nebo hash nesouhlasí)! Program se ukončuje.{Style.RESET_ALL}")
        sys.exit(1)

def main():
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
    address_book = load_address_book()
    verify_genesis_block(droid_chain)
    
    p2p_node = P2PNode(droid_chain, P2P_HOST, p2p_port, peers)
    p2p_node.server_thread.daemon = True
    p2p_node.server_thread.start()
    
    if not p2p_node.running:
        return
        
    p2p_node.sync_thread.start()
    
    print(f"\n{Fore.GREEN} Vítejte v {PROJECT_NAME} ({TICKER}) v{SOFTWARE_VERSION} {Style.RESET_ALL}")
    print(f"{Fore.CYAN}Tento uzel běží na portu {p2p_port} | Protokol v{PROTOCOL_VERSION} {Style.RESET_ALL}")
    
    while True:
        try:
            print_menu()
            try:
                choice = input(f"\n{Fore.BLUE}Zadejte číslo volby: {Style.RESET_ALL}").strip()
            except EOFError:
                choice = "12"
                
            if choice.lower() == 'clear':
                os.system('cls' if os.name == 'nt' else 'clear')
                continue
                
            if read_only and choice in ["1", "2"]:
                print(f"{Fore.RED}Chyba:{Style.RESET_ALL} Operace není povolena v read-only režimu.")
                continue
                
            if choice == "1":
                if not p2p_node.get_online_peers():
                    print(f"{Fore.RED}Chyba:{Style.RESET_ALL} Těžba není možné. Musíte být připojen k alespoň jednomu dalšímu uzlu.")
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
                    
            elif choice == "2":
                if not p2p_node.get_online_peers():
                    print(f"{Fore.RED}Chyba:{Style.RESET_ALL} Vytvoření transakce není možné. Musíte být připojen k alespoň jednomu dalšímu uzlu.")
                    continue
                    
                from_address = input(f"Zadejte ADRESU peněženky odesílatele: ")
                if from_address not in wallets:
                    print(f"{Fore.RED}Chyba:{Style.RESET_ALL} Peněženka s adresou '{from_address}' neexistuje. Nejdříve ji vytvořte nebo importujte.")
                    continue
                    
                to_address = input(f"Zadejte ADRESU příjemce: ")
                if not is_valid_address(to_address):
                    print(f"{Fore.RED}Chyba:{Style.RESET_ALL} Neplatný formát adresy příjemce.")
                    continue
                    
                if from_address == to_address:
                    print(f"{Fore.RED}Chyba:{Style.RESET_ALL} Nelze posílat peníze na stejnou adresu.")
                    continue
                    
                try:
                    amount_str = input(f"Zadejte částku: ")
                    amount_decimal = Decimal(amount_str).quantize(Decimal('1e-8'), rounding=ROUND_HALF_UP)
                    amount_in_decimal = int(amount_decimal * (10 ** DECIMALS))
                    if amount_in_decimal < MIN_TX_AMOUNT:
                        print(f"{Fore.RED}Chyba:{Style.RESET_ALL} Částka transakce je příliš malá. Minimální částka je {format(MIN_TX_AMOUNT / (10 ** DECIMALS), f'.{DECIMALS}f')} {TICKER}.")
                        continue
                except ValueError:
                    print(f"{Fore.RED}Chyba:{Style.RESET_ALL} Částka musí být číslo.")
                    continue
                    
                current_available_balance = droid_chain.get_confirmed_balance(from_address)
                for tx_in_mempool in droid_chain.unconfirmed_transactions:
                    if tx_in_mempool.from_address == from_address:
                        current_available_balance -= (tx_in_mempool.amount + tx_in_mempool.fee)
                        
                if current_available_balance < amount_in_decimal + TX_FEE_MIN:
                    print(f"{Fore.RED}Chyba:{Style.RESET_ALL} Nedostatečný zůstatek pro tuto částku (včetně min. poplatku). K dispozici: {format(Decimal(current_available_balance) / Decimal(10**DECIMALS), f'.{DECIMALS}f')} {TICKER}")
                    continue
                    
                try:
                    fee_str = input(f"Zadejte poplatek ({format(Decimal(TX_FEE_MIN)/(10**DECIMALS), f'.{DECIMALS}f')}-{format(Decimal(TX_FEE_MAX)/(10**DECIMALS), f'.{DECIMALS}f')} {TICKER}, prázdné pro {format(Decimal(TX_FEE_MIN)/(10**DECIMALS), f'.{DECIMALS}f')}): ")
                    if fee_str == "":
                        fee = TX_FEE_MIN
                    else:
                        fee_decimal = Decimal(fee_str).quantize(Decimal('1e-8'), rounding=ROUND_HALF_UP)
                        fee = int(fee_decimal * (10 ** DECIMALS))
                        if TX_FEE_MIN > fee or fee > TX_FEE_MAX:
                            print(f"{Fore.RED}Chyba:{Style.RESET_ALL} Poplatek za transakci je mimo povolený rozsah.")
                            continue
                except ValueError:
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
                print(f"\n{Fore.YELLOW}--- Blockchain ---{Style.RESET_ALL}")
                conn = sqlite3.connect(BLOCKCHAIN_DB, timeout=1.0)
                c = conn.cursor()
                c.execute("SELECT block_index, timestamp, transactions, previous_hash, target_hex, nonce, block_hash, merkle_root, version, chain_id FROM blocks ORDER BY block_index")
                rows = c.fetchall()
                conn.close()
                
                total_size = 0
                all_addresses = set()
                
                for row in rows:
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
                        'chain_id': row[9]
                    }
                    block = Block.from_dict(block_data)
                    total_size += block.get_size()
                    
                    for tx in block.transactions:
                        if tx.from_address != "COINBASE":
                            all_addresses.add(tx.from_address)
                        all_addresses.add(tx.to_address)
                        
                    target_hex = hex(block.target)[2:]
                    print(f"Blok #{block.index}")
                    print(f" Verze: {Fore.CYAN}{block.version}{Style.RESET_ALL}")
                    print(f" Chain ID: {Fore.CYAN}{block.chain_id}{Style.RESET_ALL}")
                    print(f" Hash: {Fore.MAGENTA}{block.hash}{Style.RESET_ALL}")
                    print(f" Merkle root: {Fore.CYAN}{block.merkle_root}{Style.RESET_ALL}")
                    print(f" Cílový target: {Fore.CYAN}{target_hex}{Style.RESET_ALL}")
                    print(f" Předchozí hash: {Fore.MAGENTA}{block.previous_hash}{Style.RESET_ALL}")
                    print(f" PoW Nonce: {Fore.CYAN}{block.nonce}{Style.RESET_ALL}")
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
                                print(f"   TX Nonce: {Fore.MAGENTA}{tx.nonce}{Style.RESET_ALL}")
                            if tx.signature:
                                print(f"   Podpis: {Fore.BLUE}{tx.signature}{Style.RESET_ALL}")
                            else:
                                print(f"   Podpis: {Fore.RED}žádný{Style.RESET_ALL}")
                            if tx.data:
                                print(f"   Zpráva: {Fore.YELLOW}{tx.data}{Style.RESET_ALL}")
                    print("=" * 40)
                    
                total_size_kb = total_size / 1024
                total_size_mb = total_size_kb / 1024
                
                print(f"Velikost blockchainu: {Fore.CYAN}{total_size_kb:.2f} KB / {total_size_mb:.2f} MB{Style.RESET_ALL}")
                print(f"Celkový počet bloků: {Fore.CYAN}{droid_chain.max_block_index + 1}{Style.RESET_ALL}")
                print(f"Celkový počet transakcí: {Fore.CYAN}{len(droid_chain.all_tx_ids)}{Style.RESET_ALL}")
                print(f"Celkový počet adres: {Fore.CYAN}{len(all_addresses)}{Style.RESET_ALL}")
                
            elif choice == "5":
                new_wallet = Wallet()
                wallets[new_wallet.address] = new_wallet
                print(f"{Fore.GREEN}Nová peněženka byla vytvořena!{Style.RESET_ALL}")
                print(f" Adresa: {Fore.CYAN}{new_wallet.address}{Style.RESET_ALL}")
                print(f" Privátní klíč (hex): {Fore.RED}{binascii.hexlify(new_wallet.private_key.to_string()).decode()}{Style.RESET_ALL}")
                save_data(droid_chain, wallets, password, p2p_node.peers)
                
            elif choice == "6":
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
                        
                        confirmed_dec = Decimal(confirmed_balance) / Decimal(10 ** DECIMALS)
                        total_dec = Decimal(total_balance) / Decimal(10 ** DECIMALS)
                        pending_outgoing_dec = Decimal(pending_outgoing_sum) / Decimal(10 ** DECIMALS)
                        pending_incoming_dec = Decimal(pending_incoming_sum) / Decimal(10 ** DECIMALS)
                        
                        print(f"Adresa: {Fore.CYAN}{address}{Style.RESET_ALL}")
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
                        
            elif choice == "7":
                address_to_delete = input(f"Zadejte ADRESU peněženky, kterou chcete smazat: ")
                if address_to_delete in wallets:
                    del wallets[address_to_delete]
                    print(f"{Fore.GREEN}Peněženka '{address_to_delete}' byla úspěšně smazána.{Style.RESET_ALL}")
                    save_data(droid_chain, wallets, password, p2p_node.peers)
                else:
                    print(f"{Fore.RED}Chyba:{Style.RESET_ALL} Peněženka s adresou '{address_to_delete}' neexistuje.")
                    
            elif choice == "8":
                key_hex = input(f"Zadejte privátní klíč (hex): ")
                if not is_valid_private_key(key_hex):
                    print(f"{Fore.RED}Chyba:{Style.RESET_ALL} Neplatný formát privátního klíče.")
                    continue
                imported_wallet = Wallet(private_key=key_hex)
                wallets[imported_wallet.address] = imported_wallet
                print(f"{Fore.GREEN}Peněženka byla úspěšně importována!{Style.RESET_ALL}")
                print(f" Adresa: {Fore.CYAN}{imported_wallet.address}{Style.RESET_ALL}")
                save_data(droid_chain, wallets, password, p2p_node.peers)
                
            elif choice == "9":
                address = input(f"Zadejte ADRESU peněženky, jejíž klíč chcete exportovat: ")
                if address in wallets:
                    private_key_hex = binascii.hexlify(wallets[address].private_key.to_string()).decode()
                    print(f"{Fore.GREEN}Privátní klíč pro adresu '{address}':{Style.RESET_ALL} {Fore.RED}{private_key_hex}{Style.RESET_ALL}")
                else:
                    print(f"{Fore.RED}Chyba:{Style.RESET_ALL} Peněženka s adresou '{address}' neexistuje.")
                    
            elif choice == "10":
                while True:
                    print(f"\n{Fore.YELLOW}--- Uložené adresy ---{Style.RESET_ALL}")
                    if not address_book:
                        print(f"{Fore.CYAN}Žádné uložené adresy.{Style.RESET_ALL}")
                    else:
                        for name, addr in address_book.items():
                            print(f" Jméno: {Fore.GREEN}{name}{Style.RESET_ALL} | Adresa: {Fore.CYAN}{addr}{Style.RESET_ALL}")
                    print(f"\n{Fore.GREEN}1{Style.RESET_ALL} - Přidat adresu")
                    print(f"{Fore.GREEN}2{Style.RESET_ALL} - Smazat adresu")
                    print(f"{Fore.GREEN}3{Style.RESET_ALL} - Zpět")
                    sub_choice = input(f"{Fore.BLUE}Zadejte volbu: {Style.RESET_ALL}").strip()
                    
                    if sub_choice == "1":
                        name = input("Zadejte jméno (alias): ").strip()
                        addr = input("Zadejte adresu: ").strip()
                        if not is_valid_address(addr):
                            print(f"{Fore.RED}Neplatný formát adresy.{Style.RESET_ALL}")
                        else:
                            address_book[name] = addr
                            save_address_book(address_book)
                            print(f"{Fore.GREEN}Adresa '{name}' byla uložena.{Style.RESET_ALL}")
                    elif sub_choice == "2":
                        name = input("Zadejte jméno ke smazání: ").strip()
                        if name in address_book:
                            del address_book[name]
                            save_address_book(address_book)
                            print(f"{Fore.GREEN}Adresa '{name}' byla smazána.{Style.RESET_ALL}")
                        else:
                            print(f"{Fore.RED}Jméno '{name}' nenalezeno.{Style.RESET_ALL}")
                    elif sub_choice == "3":
                        break
                    else:
                        print(f"{Fore.RED}Neplatná volba.{Style.RESET_ALL}")
                
            elif choice == "11":
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
                        print(f"  {Fore.CYAN}{peer[0]}:{peer[1]}{Style.RESET_ALL} {status}")
                        
            elif choice == "12":
                p2p_node.running = False
                print(f"\n{Fore.YELLOW}Ukládám a vypínám...{Style.RESET_ALL}")
                save_data(droid_chain, wallets, password, p2p_node.peers)
                if os.path.exists(MEMPOOL_DB):
                    os.remove(MEMPOOL_DB)
                    print(f"{Fore.GREEN}Mempool databáze byla smazána.{Style.RESET_ALL}")
                break
                
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
                            
                        confirmations = droid_chain.max_block_index - block_index + 1
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
                total_coins = sent_amount + received_amount
                total_count = sent_count + received_count
                
                confirmed_dec = Decimal(confirmed_balance) / Decimal(10 ** DECIMALS)
                sent_dec = Decimal(sent_amount) / Decimal(10 ** DECIMALS)
                received_dec = Decimal(received_amount) / Decimal(10 ** DECIMALS)
                total_coins_dec = Decimal(total_coins) / Decimal(10 ** DECIMALS)
                
                print(f"\n{Fore.YELLOW}--- Statistiky historie transakcí ---{Style.RESET_ALL}")
                print(f"Potvrzený zůstatek: {Fore.MAGENTA}{format(confirmed_dec, f'.{DECIMALS}f')} {TICKER}{Style.RESET_ALL}")
                print(f"Odeslané mince: {Fore.RED}{format(sent_dec, f'.{DECIMALS}f')} {TICKER}{Style.RESET_ALL}")
                print(f"Přijaté mince: {Fore.GREEN}{format(received_dec, f'.{DECIMALS}f')} {TICKER}{Style.RESET_ALL}")
                print(f"Součet mincí: {Fore.CYAN}{format(total_coins_dec, f'.{DECIMALS}f')} {TICKER}{Style.RESET_ALL}")
                print(f"Odeslané transakce: {Fore.RED}{sent_count}{Style.RESET_ALL}")
                print(f"Přijaté transakce: {Fore.GREEN}{received_count}{Style.RESET_ALL}")
                print(f"Celkový počet: {Fore.CYAN}{total_count}{Style.RESET_ALL}")
                if pending_list:
                    print(f"Čekající transakce: {Fore.YELLOW}{len(pending_list)}{Style.RESET_ALL}")
                    
            elif choice == "14":
                show_p2p_log()
                
            elif choice == "15":
                tx_id = input("Zadejte TX ID transakce: ")
                tx, location = droid_chain.find_transaction_by_id(tx_id)
                if tx:
                    print(f"\n{Fore.YELLOW}--- Detaily transakce (TX ID: {tx.tx_id}) ---{Style.RESET_ALL}")
                    print(f" Stav: {Fore.GREEN}Nalezena v {location}{Style.RESET_ALL}")
                    if "Blok #" in location:
                        block_index = int(location.split("#")[1])
                        confirmations = droid_chain.max_block_index - block_index + 1
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
                    
            elif choice == "16":
                total_supply = droid_chain.get_total_supply()
                max_supply = MAX_SUPPLY
                print(f"\n{Fore.YELLOW}--- Celková nabídka mincí ---{Style.RESET_ALL}")
                print(f" Celková nabídka: {Fore.CYAN}{format(Decimal(total_supply) / Decimal(10 ** DECIMALS), f'.{DECIMALS}f')} {TICKER}{Style.RESET_ALL}")
                print(f" Maximální nabídka: {Fore.CYAN}{format(Decimal(max_supply) / Decimal(10 ** DECIMALS), f'.{DECIMALS}f')} {TICKER}{Style.RESET_ALL}")
                
            elif choice == "17":
                block_hash = input("Zadejte hash bloku: ").strip()
                conn = sqlite3.connect(BLOCKCHAIN_DB, timeout=1.0)
                c = conn.cursor()
                c.execute("SELECT block_index, timestamp, transactions, previous_hash, target_hex, nonce, block_hash, merkle_root, version, chain_id FROM blocks WHERE block_hash = ?", (block_hash,))
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
                        'chain_id': row[9]
                    }
                    block = Block.from_dict(block_data)
                    target_hex = hex(block.target)[2:]
                    print(f"\n{Fore.GREEN}Blok nalezen!{Style.RESET_ALL}")
                    print(f"Blok #{block.index}")
                    print(f" Verze: {Fore.CYAN}{block.version}{Style.RESET_ALL}")
                    print(f" Chain ID: {Fore.CYAN}{block.chain_id}{Style.RESET_ALL}")
                    print(f" Hash: {Fore.MAGENTA}{block.hash}{Style.RESET_ALL}")
                    print(f" Merkle root: {Fore.CYAN}{block.merkle_root}{Style.RESET_ALL}")
                    print(f" Cílový target: {Fore.CYAN}{target_hex}{Style.RESET_ALL}")
                    print(f" Předchozí hash: {Fore.MAGENTA}{block.previous_hash}{Style.RESET_ALL}")
                    print(f" PoW Nonce: {Fore.CYAN}{block.nonce}{Style.RESET_ALL}")
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
                                print(f"   TX Nonce: {Fore.MAGENTA}{tx.nonce}{Style.RESET_ALL}")
                            if tx.signature:
                                print(f"   Podpis: {Fore.BLUE}{tx.signature}{Style.RESET_ALL}")
                            else:
                                print(f"   Podpis: {Fore.RED}žádný{Style.RESET_ALL}")
                            if tx.data:
                                print(f"   Zpráva: {Fore.YELLOW}{tx.data}{Style.RESET_ALL}")
                    print("=" * 40)
                else:
                    print(f"{Fore.RED}Blok s hashem {block_hash} nebyl nalezen.{Style.RESET_ALL}")
                
            elif choice == "18":
                peer_ip = input("Zadejte IP adresu uzlu k přidání: ")
                peer_port = int(input("Zadejte port uzlu: "))
                new_peer = (peer_ip, peer_port)
                if new_peer not in p2p_node.peers:
                    p2p_node.peers.append(new_peer)
                    save_peers(p2p_node.peers)
                    print(f"{Fore.GREEN}Uzel {new_peer} byl přidán do seznamu.{Style.RESET_ALL}")
                else:
                    print(f"{Fore.YELLOW}Uzel {new_peer} již v seznamu existuje.{Style.RESET_ALL}")
                    
            elif choice == "19":
                if p2p_node.peers:
                    print(f"\n{Fore.YELLOW}--- Uložené uzly ---{Style.RESET_ALL}")
                    for i, peer in enumerate(p2p_node.peers, 1):
                        print(f"{i}. {peer[0]}:{peer[1]}")
                else:
                    print(f"{Fore.YELLOW}Žádné uzly nejsou uloženy.{Style.RESET_ALL}")
                    continue
                    
                peer_ip = input("Zadejte IP adresu uzlu k odstranění: ")
                try:
                    peer_port = int(input("Zadejte port uzlu k odstranění: "))
                except ValueError:
                    print(f"{Fore.RED}Neplatný port.{Style.RESET_ALL}")
                    continue
                    
                peer_to_remove = (peer_ip, peer_port)
                if peer_to_remove in p2p_node.peers:
                    p2p_node.peers.remove(peer_to_remove)
                    save_peers(p2p_node.peers)
                    print(f"{Fore.GREEN}Uzel {peer_to_remove} byl odstraněn.{Style.RESET_ALL}")
                else:
                    print(f"{Fore.RED}Uzel {peer_to_remove} není v seznamu.{Style.RESET_ALL}")
                    
            elif choice == "20":
                try:
                    block_index = int(input("Zadejte číslo bloku: "))
                    if 0 <= block_index <= droid_chain.max_block_index:
                        block = droid_chain.get_block(block_index)
                        target_hex = hex(block.target)[2:]
                        print(f"Blok #{block.index}")
                        print(f" Verze: {Fore.CYAN}{block.version}{Style.RESET_ALL}")
                        print(f" Chain ID: {Fore.CYAN}{block.chain_id}{Style.RESET_ALL}")
                        print(f" Hash: {Fore.MAGENTA}{block.hash}{Style.RESET_ALL}")
                        print(f" Merkle root: {Fore.CYAN}{block.merkle_root}{Style.RESET_ALL}")
                        print(f" Cílový target: {Fore.CYAN}{target_hex}{Style.RESET_ALL}")
                        print(f" Předchozí hash: {Fore.MAGENTA}{block.previous_hash}{Style.RESET_ALL}")
                        print(f" PoW Nonce: {Fore.CYAN}{block.nonce}{Style.RESET_ALL}")
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
                                    print(f"   TX Nonce: {Fore.MAGENTA}{tx.nonce}{Style.RESET_ALL}")
                                if tx.signature:
                                    print(f"   Podpis: {Fore.BLUE}{tx.signature}{Style.RESET_ALL}")
                                else:
                                    print(f"   Podpis: {Fore.RED}žádný{Style.RESET_ALL}")
                                if tx.data:
                                    print(f"   Zpráva: {Fore.YELLOW}{tx.data}{Style.RESET_ALL}")
                        print("=" * 40)
                    else:
                        print(f"{Fore.RED}Blok s číslem {block_index} neexistuje.{Style.RESET_ALL}")
                except ValueError:
                    print(f"{Fore.RED}Neplatné číslo bloku.{Style.RESET_ALL}")
            else:
                print(f"{Fore.RED}Neplatná volba. Zkuste to prosím znovu.{Style.RESET_ALL}")
                
        except KeyboardInterrupt:
            print(f"\n{Fore.YELLOW}Ukončuji program (CTRL+C)...{Style.RESET_ALL}")
            if 'p2p_node' in globals() and p2p_node:
                p2p_node.running = False
            save_data(droid_chain, wallets, password, p2p_node.peers if 'p2p_node' in globals() and p2p_node else [])
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
