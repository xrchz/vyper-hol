@external
def foo() -> uint256:
    y: uint256 = 0
    for i: uint256 in range(2):
        y = y + i
    return y
