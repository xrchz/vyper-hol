event Ping:
    indexed_value: indexed(uint256)
    data_value: uint256

@external
def foo(x: uint256, y: uint256):
    log Ping(indexed_value=x, data_value=y)
