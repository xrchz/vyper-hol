@external
def foo(x: bool) -> uint256:
    y: uint256 = 1
    if x:
        y = 2
    else:
        y = 3
    return y
