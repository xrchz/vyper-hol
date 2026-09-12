event Ping:
    value: indexed(uint256)

@external
def foo(x: uint256):
    log Ping(value=x)
