import oracle

@external
@view
def read(addr: address, x: uint256) -> uint256:
    return staticcall oracle(addr).read_value(x)
