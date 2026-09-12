@external
def foo() -> uint256:
    y: uint256 = 0
    for i: uint256 in range(3):
        if i == 1:
            continue
        y = y + i
    return y
