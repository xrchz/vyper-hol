#pragma version 0.5.0a3

struct Params:
    salt: bytes32
    collateral_token: address
    borrow_token: address

@external
@view
def hash_params(params: Params) -> bytes32:
    return keccak256(abi_encode(msg.sender, params.salt, params.collateral_token, params.borrow_token))
