"""
Reference operations come from `py_ecc.bls.G2ProofOfPossession`.
"""

from py_ecc.bls import G2ProofOfPossession as ref_bls


# ---- Messages -------------------------------------------------------------

MESSAGES = [
    b"\x00" * 32,
    b"\x56" * 32,
    b"\xab" * 32,
]
SAMPLE_MESSAGE = b"\x12" * 32


# ---- Private keys ---------------------------------------------------------

PRIVKEYS = [
    0x263dbd792f5b1be47ed85f8938c0f29586af0d3ac7b977f21c278fe1462040e3,
    0x47b8192d77bf871b62e87859d653922725724a5c031afeabc60bcef5ff665138,
    0x328388aff0d4a5b7dc9205abd374e7e98f3cd9f3418edb4eafda5fb16473d216,
]


# ---- Compressed-G group encodings ----------------------------------------

ZERO_PUBKEY          = b"\x00" * 48
G1_POINT_AT_INFINITY = b"\xc0" + b"\x00" * 47
ZERO_SIGNATURE       = b"\x00" * 96
G2_POINT_AT_INFINITY = b"\xc0" + b"\x00" * 95


# ---- Helpers --------------------------------------------------------------

def sk_to_pk(sk: int) -> bytes:
    return ref_bls.SkToPk(sk)


def sign(sk: int, msg: bytes) -> bytes:
    return ref_bls.Sign(sk, msg)


def aggregate(sigs: list[bytes]) -> bytes:
    return ref_bls.Aggregate(sigs)
